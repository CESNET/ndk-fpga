# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Reference model for AXIS_ETH_PARSER verification.

This module contains the reference model that parses packets using a pipeline
approach, matching the behavior of the AXIS_ETH_PARSER DUT.

The model implements a chain of parsing stages where each stage:
1. Receives expected protocol type and offset from the previous stage
2. Checks if it can parse this protocol type
3. If yes: parses the protocol and passes next protocol info to the next stage
4. If no: passes the input info unchanged to the next stage

Supported protocol chain: ETH -> [VLAN] -> IPv4 -> TCP
- VLAN is optional (max 1 tag)
- IPv4 is parsed only if ethertype indicates IPv4 (0x0800)
- TCP is parsed only if IPv4 protocol field indicates TCP (6)
"""

from dataclasses import dataclass

from scoreboard import AxisEthParserResult


@dataclass
class ParserStageInfo:
    """Information passed between parsing stages.

    Each stage receives this info from the previous stage and either:
    - Uses it to parse the protocol (if it matches the expected type)
    - Passes it unchanged to the next stage (if it doesn't match)

    Attributes:
        protocol_type: Expected protocol type to parse (e.g., 'ETH', 'VLAN', 'IPv4', 'TCP')
        offset: Byte offset in packet data where this protocol starts
        valid: Whether this stage should attempt parsing (False = pass through)
    """
    protocol_type: str
    offset: int
    valid: bool = True


class AxisEthParserModel:
    """Reference model for AXIS_ETH_PARSER.

    This class implements the reference model using a pipeline of parsing stages.
    Each stage receives protocol information from the previous stage, decides
    whether to parse, and passes updated information to the next stage.

    The pipeline structure mirrors the actual hardware implementation where
    each parsing unit is specialized for a specific protocol and receives
    control information from the previous unit.

    Protocol chain: ETH -> [VLAN] -> IPv4 -> TCP
    """

    # Protocol type constants
    PROTO_ETH = 'ETH'
    PROTO_VLAN = 'VLAN'
    PROTO_IPV4 = 'IPv4'
    PROTO_TCP = 'TCP'
    PROTO_NONE = 'NONE'

    # Ethertype constants
    ETHERTYPE_VLAN = 0x8100
    ETHERTYPE_IPV4 = 0x0800

    # IP protocol constants
    IP_PROTOCOL_TCP = 6

    def __init__(self):
        """Initialize the reference model."""
        self.pkts_processed = 0

    @staticmethod
    def mac_to_int(mac_bytes: bytes) -> int:
        """Convert MAC address bytes to integer.

        Args:
            mac_bytes: MAC address as 6 bytes

        Returns:
            int: MAC address as integer
        """
        return int.from_bytes(mac_bytes, 'big')

    @staticmethod
    def _ip_to_int(ip_bytes: bytes) -> int:
        """Convert IPv4 address bytes to integer.

        Args:
            ip_bytes: IPv4 address as 4 bytes

        Returns:
            int: IP address as 32-bit integer
        """
        return int.from_bytes(ip_bytes, 'big')

    def extract_headers(self, pkt, packet_bytes: bytes = None) -> AxisEthParserResult:
        """Extract header information from a packet using pipeline stages.

        This method implements a pipeline of parsing stages where each stage
        receives protocol information from the previous stage and either parses
        the protocol or passes the information through.

        Args:
            pkt: Scapy packet object (for compatibility, not used for parsing)
            packet_bytes: Raw packet bytes for parsing

        Returns:
            AxisEthParserResult: Extracted header information
        """
        result = AxisEthParserResult()
        result.packet_bytes = packet_bytes if packet_bytes is not None else raw(pkt)
        data = result.packet_bytes

        if len(data) < 14:
            # Packet too short for Ethernet header
            self.pkts_processed += 1
            return result

        # Stage 1: Ethernet Parser
        # Initial stage always expects ETH at offset 0
        eth_info = ParserStageInfo(self.PROTO_ETH, 0)
        next_info = self._parse_eth(data, result, eth_info)

        # Stage 2: VLAN Parser
        next_info = self._parse_vlan(data, result, next_info)

        # Stage 3: IPv4 Parser
        next_info = self._parse_ipv4(data, result, next_info)

        # Stage 4: TCP Parser
        self._parse_tcp(data, result, next_info)

        self.pkts_processed += 1
        return result

    def _parse_eth(self, data: bytes, result: AxisEthParserResult,
                   stage_info: ParserStageInfo) -> ParserStageInfo:
        """Ethernet parsing stage.

        Parses Ethernet header if stage_info indicates ETH protocol.
        Returns info for the next stage (VLAN or IPv4 or NONE).

        Ethernet header format (14 bytes):
        - Destination MAC: 6 bytes
        - Source MAC: 6 bytes
        - Ethertype: 2 bytes

        Args:
            data: Raw packet bytes
            result: Result object to populate
            stage_info: Protocol info from previous stage

        Returns:
            ParserStageInfo: Info for the next stage
        """
        # Check if we should parse ETH
        if stage_info.protocol_type != self.PROTO_ETH or not stage_info.valid:
            # Pass through - this shouldn't happen for ETH as it's the first stage
            return stage_info

        offset = stage_info.offset

        if len(data) < offset + 14:
            # Packet too short for Ethernet header
            return ParserStageInfo(self.PROTO_NONE, offset, False)

        # Parse Ethernet header
        result.eth_dst_mac = self.mac_to_int(data[offset:offset + 6])
        result.eth_src_mac = self.mac_to_int(data[offset + 6:offset + 12])
        result.eth_ethertype = int.from_bytes(data[offset + 12:offset + 14], 'big')
        result.eth_vld = 1
        result.eth_offset = offset

        # Determine next protocol based on ethertype
        if result.eth_ethertype == self.ETHERTYPE_VLAN:
            return ParserStageInfo(self.PROTO_VLAN, offset + 14)
        elif result.eth_ethertype == self.ETHERTYPE_IPV4:
            return ParserStageInfo(self.PROTO_IPV4, offset + 14)
        else:
            return ParserStageInfo(self.PROTO_NONE, offset + 14, False)

    def _parse_vlan(self, data: bytes, result: AxisEthParserResult,
                    stage_info: ParserStageInfo) -> ParserStageInfo:
        """VLAN parsing stage.

        Parses VLAN header if stage_info indicates VLAN protocol.
        Returns info for the next stage (IPv4 or NONE).

        VLAN header format (4 bytes):
        - TPID: 2 bytes (0x8100 for 802.1Q)
        - TCI: 2 bytes (PCP[3] + DEI[1] + VID[12])
        - Encapsulated ethertype follows VLAN header

        Args:
            data: Raw packet bytes
            result: Result object to populate
            stage_info: Protocol info from previous stage

        Returns:
            ParserStageInfo: Info for the next stage
        """
        # Check if we should parse VLAN
        if stage_info.protocol_type != self.PROTO_VLAN or not stage_info.valid:
            # Pass through - VLAN not present
            return stage_info

        offset = stage_info.offset

        if len(data) < offset + 4:
            # Packet too short for VLAN header
            return ParserStageInfo(self.PROTO_NONE, offset, False)

        # Parse VLAN TCI (bytes 0-1 of VLAN header)
        tci = int.from_bytes(data[offset:offset + 2], 'big')
        result.vlan_tci = tci

        # Parse encapsulated ethertype (bytes 2-3 of VLAN header)
        vlan_ethertype = int.from_bytes(data[offset + 2:offset + 4], 'big')
        result.vlan_ethertype = vlan_ethertype
        result.vlan_vld = 1
        result.vlan_offset = offset

        # Determine next protocol based on encapsulated ethertype
        if vlan_ethertype == self.ETHERTYPE_IPV4:
            return ParserStageInfo(self.PROTO_IPV4, offset + 4)
        else:
            return ParserStageInfo(self.PROTO_NONE, offset + 4, False)

    def _parse_ipv4(self, data: bytes, result: AxisEthParserResult,
                    stage_info: ParserStageInfo) -> ParserStageInfo:
        """IPv4 parsing stage.

        Parses IPv4 header if stage_info indicates IPv4 protocol.
        Returns info for the next stage (TCP or NONE).

        IPv4 header format (minimum 20 bytes):
        - Version (4 bits) + IHL (4 bits): 1 byte
        - TOS: 1 byte
        - Total Length: 2 bytes
        - Identification: 2 bytes
        - Flags (3 bits) + Fragment Offset (13 bits): 2 bytes
        - TTL: 1 byte
        - Protocol: 1 byte
        - Header Checksum: 2 bytes
        - Source IP: 4 bytes
        - Destination IP: 4 bytes

        Args:
            data: Raw packet bytes
            result: Result object to populate
            stage_info: Protocol info from previous stage

        Returns:
            ParserStageInfo: Info for the next stage
        """
        # Check if we should parse IPv4
        if stage_info.protocol_type != self.PROTO_IPV4 or not stage_info.valid:
            # Pass through - IPv4 not present
            return stage_info

        offset = stage_info.offset

        if len(data) < offset + 20:
            # Packet too short for IPv4 header
            return ParserStageInfo(self.PROTO_NONE, offset, False)

        # Parse IPv4 header
        # First byte contains IHL (bits 0-3) and Version (bits 4-7)
        version_ihl = data[offset]
        result.ipv4_ihl = version_ihl & 0xF          # IHL: bits [3:0]
        result.ipv4_version = (version_ihl >> 4) & 0xF  # Version: bits [7:4]

        result.ipv4_tos = data[offset + 1]
        result.ipv4_total_length = int.from_bytes(data[offset + 2:offset + 4], 'big')
        result.ipv4_identification = int.from_bytes(data[offset + 4:offset + 6], 'big')

        flags_frag = int.from_bytes(data[offset + 6:offset + 8], 'big')
        result.ipv4_flags = (flags_frag >> 13) & 0x7
        result.ipv4_fragment_offset = flags_frag & 0x1FFF

        result.ipv4_ttl = data[offset + 8]
        result.ipv4_protocol = data[offset + 9]
        result.ipv4_header_checksum = int.from_bytes(data[offset + 10:offset + 12], 'big')

        result.ipv4_src_ip = self._ip_to_int(data[offset + 12:offset + 16])
        result.ipv4_dst_ip = self._ip_to_int(data[offset + 16:offset + 20])

        result.ipv4_vld = 1
        result.ipv4_offset = offset

        # Determine next protocol based on IP protocol field
        if result.ipv4_protocol == self.IP_PROTOCOL_TCP:
            # Calculate TCP offset based on IP header length (IHL * 4 bytes)
            ip_hdr_len = result.ipv4_ihl * 4
            tcp_offset = offset + ip_hdr_len
            return ParserStageInfo(self.PROTO_TCP, tcp_offset)
        else:
            return ParserStageInfo(self.PROTO_NONE, offset, False)

    def _parse_tcp(self, data: bytes, result: AxisEthParserResult,
                   stage_info: ParserStageInfo) -> ParserStageInfo:
        """TCP parsing stage.

        Parses TCP header if stage_info indicates TCP protocol.

        TCP header format (minimum 20 bytes):
        - Source Port: 2 bytes
        - Destination Port: 2 bytes
        - Sequence Number: 4 bytes
        - Acknowledgment Number: 4 bytes
        - Data Offset (4 bits) + Reserved (3 bits) + Flags (9 bits): 2 bytes
        - Window Size: 2 bytes
        - Checksum: 2 bytes
        - Urgent Pointer: 2 bytes

        Args:
            data: Raw packet bytes
            result: Result object to populate
            stage_info: Protocol info from previous stage

        Returns:
            ParserStageInfo: Info for the next stage (always NONE for now)
        """
        # Check if we should parse TCP
        if stage_info.protocol_type != self.PROTO_TCP or not stage_info.valid:
            # Pass through - TCP not present
            return ParserStageInfo(self.PROTO_NONE, stage_info.offset, False)

        offset = stage_info.offset

        if len(data) < offset + 20:
            # Packet too short for TCP header
            return ParserStageInfo(self.PROTO_NONE, offset, False)

        # Parse TCP header
        result.tcp_src_port = int.from_bytes(data[offset:offset + 2], 'big')
        result.tcp_dst_port = int.from_bytes(data[offset + 2:offset + 4], 'big')
        result.tcp_seq_num = int.from_bytes(data[offset + 4:offset + 8], 'big')
        result.tcp_ack_num = int.from_bytes(data[offset + 8:offset + 12], 'big')

        data_offset_flags = int.from_bytes(data[offset + 12:offset + 14], 'big')
        result.tcp_data_offset = (data_offset_flags >> 12) & 0xF
        result.tcp_reserved = (data_offset_flags >> 9) & 0x7
        result.tcp_flags = data_offset_flags & 0x1FF

        result.tcp_window = int.from_bytes(data[offset + 14:offset + 16], 'big')
        result.tcp_checksum = int.from_bytes(data[offset + 16:offset + 18], 'big')
        result.tcp_urgent_ptr = int.from_bytes(data[offset + 18:offset + 20], 'big')

        result.tcp_vld = 1
        result.tcp_offset = offset

        # No further parsing stages
        return ParserStageInfo(self.PROTO_NONE, offset, False)
