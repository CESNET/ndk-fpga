# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import random
from typing import Optional, Tuple

from scapy.all import Ether, Dot1Q, IP, IPv6, TCP, UDP, ICMPv6EchoRequest, SCTP, Raw, raw, Packet
from scapy.contrib.mpls import MPLS


class ScapyPacketGenerator:
    """Generic packet generator using Scapy for network testing.

    This class provides static methods to generate random Ethernet packets with
    various protocol combinations (IPv4/IPv6, TCP/UDP/SCTP/ICMPv6) and optional
    VLAN/MPLS tagging. It also provides methods to extract protocol metadata
    such as header offsets, lengths, and checksums.

    Supported protocol stacks:
        - Ethernet + [VLAN/QinQ] + [MPLS] + IPv4/IPv6 + TCP/UDP/SCTP/ICMPv6

    Example:
        >>> pkt = ScapyPacketGenerator.generate(min_len=64, max_len=256)
        >>> l3_offset, l3_len, proto, csum_en, csum = ScapyPacketGenerator.get_l3_info(pkt)
        >>> l4_offset, l4_len, proto, csum_en, csum = ScapyPacketGenerator.get_l4_info(pkt, l3_len)
    """

    @staticmethod
    def generate(min_len: int = 60, max_len: int = 1518) -> Packet:
        """Generate a random Ethernet packet with various protocol layers.

        Creates packets with random combinations of:
        - L2: Ethernet with optional VLAN (0-2 tags) and/or MPLS (0-2 labels)
        - L3: IPv4 or IPv6 (randomly selected)
        - L4: TCP, UDP, SCTP, or ICMPv6 (randomly selected, protocol-dependent)

        Args:
            min_len: Minimum total packet length in bytes (default: 60, minimum: 60).
            max_len: Maximum total packet length in bytes (default: 1518).

        Returns:
            Packet: A Scapy packet object with all layers built.

        Raises:
            AssertionError: If min_len < 60 or max_len < min_len.
        """
        assert min_len >= 60
        assert max_len >= min_len

        # Random IPv4 / IPv6
        ipv6_en = random.choice([True, False])

        if ipv6_en:
            src_ip = ":".join(f"{random.randint(0, 0xffff):x}" for _ in range(8))
            dst_ip = ":".join(f"{random.randint(0, 0xffff):x}" for _ in range(8))
            ip_layer = IPv6(src=src_ip, dst=dst_ip)
        else:
            src_ip = ".".join(str(random.randint(1, 254)) for _ in range(4))
            dst_ip = ".".join(str(random.randint(1, 254)) for _ in range(4))
            ip_layer = IP(src=src_ip, dst=dst_ip)

        # Random L4 (TCP/UDP/ICMPv6/SCTP_no_crc)
        l4_choice = random.choice(["tcp", "udp", "icmpv6", "sctp"])  # 25% each

        if l4_choice == "tcp":
            l4_layer = TCP(
                sport=random.randint(1024, 65535),
                dport=random.randint(1, 65535)
            )
        elif l4_choice == "udp":
            l4_layer = UDP(
                sport=random.randint(1024, 65535),
                dport=random.randint(1, 65535)
            )
        elif l4_choice == "sctp":
            # SCTP with disabled checksum (chksum=0)
            l4_layer = SCTP(
                sport=random.randint(1024, 65535),
                dport=random.randint(1, 65535),
                chksum=0
            )
        elif ipv6_en:
            # ICMPv6 for IPv6
            l4_layer = ICMPv6EchoRequest(
                id=random.randint(0, 65535),
                seq=random.randint(0, 65535)
            )
        else:
            # For IPv4 without ICMPv4, use UDP
            l4_layer = UDP(
                sport=random.randint(1024, 65535),
                dport=random.randint(1, 65535)
            )

        # Payload length control
        base_pkt = Ether() / ip_layer / l4_layer
        base_len = len(raw(base_pkt))

        payload_len = random.randint(
            max(0, min_len - base_len),
            max_len - base_len
        )

        payload = Raw(bytes(random.getrandbits(8) for _ in range(payload_len)))

        # Build packet from back to front
        pkt = ip_layer / l4_layer / payload

        # Optional MPLS (random 0-2 labels)
        mpls_count = random.choice([0, 0, 0, 1, 1, 2])  # 50% no MPLS, 33% 1 label, 17% 2 labels
        for _ in range(mpls_count):
            mpls_label = random.randint(16, 1048575)  # Valid MPLS label range
            mpls_ttl = random.randint(1, 255)
            pkt = MPLS(label=mpls_label, ttl=mpls_ttl) / pkt

        # Optional VLAN/QinQ (0, 1 or 2 VLAN tags)
        vlan_count = random.choice([0, 1, 1, 2])  # 25% no VLAN, 50% 1 VLAN, 25% QinQ
        for _ in range(vlan_count):
            vlan = Dot1Q(vlan=random.randint(1, 4094))
            pkt = vlan / pkt

        # Add Ethernet header
        eth = Ether()
        pkt = eth / pkt

        # Force checksum calculation
        pkt = pkt.__class__(raw(pkt))

        return pkt

    @staticmethod
    def _get_l3_offset(pkt: Packet) -> int:
        """Calculate L3 (IP) offset from Ethernet packet.

        Counts Ethernet header (14 bytes) + VLAN tags (4 bytes each) + MPLS labels (4 bytes each).

        Args:
            pkt: Scapy packet object starting with Ethernet header.

        Returns:
            Byte offset where the IP layer begins.
        """
        offset = 14  # Ethernet header is always 14 bytes

        # Count VLAN tags and MPLS labels by walking through packet layers
        vlan_count = 0
        mpls_count = 0
        current = pkt.payload  # Start after Ethernet header

        while current is not None:
            # Stop when we reach the IP layer
            if isinstance(current, (IP, IPv6)):
                break

            if isinstance(current, Dot1Q):
                vlan_count += 1
            elif isinstance(current, MPLS):
                mpls_count += 1

            # Move to next layer
            current = current.payload if hasattr(current, 'payload') and current.payload else None

        offset += vlan_count * 4
        offset += mpls_count * 4

        return offset

    @staticmethod
    def get_l3_info(pkt: Packet) -> Tuple[int, int, int, int, Optional[int]]:
        """Extract L3 (IP) layer information from a packet.

        Args:
            pkt: Scapy packet containing an IP layer.

        Returns:
            A tuple containing:
                - l3_offset (int): Byte offset to the start of the IP header.
                - l3_length (int): Length of the IP header in bytes (20-60 for IPv4, 40 for IPv6).
                - l3_proto_number (int): IP protocol version (4 for IPv4, 6 for IPv6).
                - l3_csum_en (int): Checksum enable flag (1 for IPv4, 0 for IPv6).
                - l3_checksum (Optional[int]): Header checksum value for IPv4, None for IPv6.

        Raises:
            ValueError: If the packet does not contain an IPv4 or IPv6 layer.
        """
        l3_offset = ScapyPacketGenerator._get_l3_offset(pkt)

        if pkt.haslayer(IPv6):
            return (l3_offset, 40, 6, 0, None)  # IPv6 has no L3 checksum
        elif pkt.haslayer(IP):
            ip_hdr_len = pkt[IP].ihl * 4
            return (l3_offset, ip_hdr_len, 4, 1, pkt[IP].chksum)
        else:
            raise ValueError("Packet has no IP layer")

    @staticmethod
    def get_l4_info(pkt: Packet, l3_length: int) -> Tuple[int, int, int, int, int]:
        """Extract L4 (transport) layer information from a packet.

        Args:
            pkt: Scapy packet containing a transport layer.
            l3_length: Length of the L3 header in bytes (from get_l3_info).

        Returns:
            A tuple containing:
                - l4_offset (int): Byte offset to the start of the L4 header.
                - l4_length (int): Length of the L4 header in bytes.
                - l4_proto_number (int): Protocol number (6 for TCP, 17 for UDP,
                  132 for SCTP, 58 for ICMPv6).
                - l4_csum_en (int): Checksum enable flag (1 for TCP/UDP/ICMPv6,
                  0 for SCTP when checksum is disabled).
                - l4_checksum (int): Checksum value (0 for SCTP when disabled).

        Raises:
            ValueError: If the packet does not contain a supported L4 layer.
        """
        l3_offset = ScapyPacketGenerator._get_l3_offset(pkt)
        l4_offset = l3_offset + l3_length

        if pkt.haslayer(TCP):
            return (l4_offset, len(raw(pkt[TCP])), 6, 1, pkt[TCP].chksum)
        elif pkt.haslayer(UDP):
            return (l4_offset, len(raw(pkt[UDP])), 17, 1, pkt[UDP].chksum)
        elif pkt.haslayer(SCTP):
            # SCTP uses CRC32, but Scapy uses chksum field. chksum=0 means disabled
            csum_val = pkt[SCTP].chksum
            csum_en = 0 if csum_val == 0 else 1
            # Return 0 as checksum value when disabled
            return (l4_offset, len(raw(pkt[SCTP])), 132, csum_en, 0)
        elif pkt.haslayer(ICMPv6EchoRequest):
            return (l4_offset, len(raw(pkt[ICMPv6EchoRequest])), 58, 1, pkt[ICMPv6EchoRequest].cksum)
        else:
            raise ValueError("Packet has no supported L4 layer (TCP/UDP/SCTP/ICMPv6)")

    @staticmethod
    def get_ip_addresses(pkt: Packet) -> Tuple[str, str]:
        """Extract source and destination IP addresses from a packet.

        Args:
            pkt: Scapy packet containing an IP layer.

        Returns:
            A tuple of (source_ip, destination_ip) as strings.
            For IPv4: dotted decimal notation (e.g., "192.168.1.1").
            For IPv6: colon-separated hexadecimal (e.g., "2001:db8::1").

        Raises:
            ValueError: If the packet does not contain an IPv4 or IPv6 layer.
        """
        if pkt.haslayer(IPv6):
            src_ip = pkt[IPv6].src
            dst_ip = pkt[IPv6].dst
        elif pkt.haslayer(IP):
            src_ip = pkt[IP].src
            dst_ip = pkt[IP].dst
        else:
            raise ValueError("Packet has no IP layer")

        return (src_ip, dst_ip)
