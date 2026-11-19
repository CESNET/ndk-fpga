# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Packet generator for the AXIS_ETH_PARSER test.

The generator builds packets byte by byte from a Stack, which describes the
headers of the packet. It can create header stacks and header fields that a
regular packet library does not allow.
"""

import itertools
import random
from dataclasses import dataclass
from typing import List, Tuple

ETH_TYPE_IPV4 = 0x0800
ETH_TYPE_IPV6 = 0x86DD
ETH_TYPE_MPLS = [0x8847, 0x8848]
VLAN_TPIDS = [0x8100, 0x88A8, 0x9100]
OTHER_ETH_TYPES = [0x0806, 0x8863, 0x8864, 0x88CC, 0x1234]

IP_PROTO_TCP = 6
IP_PROTO_UDP = 17
# Protocols after IPv4 that the parser does not read (ICMP, ESP, ICMPv6, IPv6 Routing)
IPV4_PROTO_OTHER = [1, 50, 58, 43]
# Protocols after IPv6 that the parser does not read (ICMP, ESP, ICMPv6, No Next Header)
IPV6_PROTO_OTHER = [1, 50, 58, 59]
IPV6_EXT_TYPES = [0, 43, 60, 44]
IPV6_EXT_FRAGMENT = 44

MAX_VLAN = 3
MAX_MPLS = 3
MAX_IPV6_EXT = 3


@dataclass
class Stack:
    """Headers of one packet.

    l3 is "ipv4", "ipv6" or "other". l4 is an IP protocol number.
    ext_lens are the hdr_ext_len values of the IPv6 extension headers.
    """
    tpids: Tuple[int, ...] = ()
    mpls_cnt: int = 0
    mpls_type: int = 0x8847
    l3: str = "ipv4"
    other_type: int = 0x0806
    ihl: int = 5
    ext_types: Tuple[int, ...] = ()
    ext_lens: Tuple[int, ...] = ()
    l4: int = IP_PROTO_TCP
    tcp_data_offset: int = 5

    def name(self) -> str:
        parts = ["eth"] + ["vlan"] * len(self.tpids) + ["mpls"] * self.mpls_cnt
        if self.l3 == "other":
            return "-".join(parts + ["other"])
        parts += [self.l3] + ["ipv6ext"] * len(self.ext_types)
        l4 = {IP_PROTO_TCP: "tcp", IP_PROTO_UDP: "udp"}.get(self.l4, "other")
        return "-".join(parts + [l4])


def rand_bytes(n: int) -> bytes:
    return bytes(random.getrandbits(8) for _ in range(n))


def u16(v: int) -> bytes:
    return v.to_bytes(2, "big")


def build_stack(st: Stack, min_len: int = 60, payload_max: int = 64) -> Tuple[bytes, List[int]]:
    """Build a packet with the headers in st.

    Returns:
        The packet and the offsets where each header ends.
    """
    if st.mpls_cnt > 0:
        l2_end_type = st.mpls_type
    else:
        l2_end_type = {"ipv4": ETH_TYPE_IPV4, "ipv6": ETH_TYPE_IPV6}.get(st.l3, st.other_type)
    types = list(st.tpids) + [l2_end_type]
    ends = []

    pkt = rand_bytes(12) + u16(types[0])
    ends.append(len(pkt))
    for i in range(len(st.tpids)):
        pkt += rand_bytes(2) + u16(types[i + 1])
        ends.append(len(pkt))

    for i in range(st.mpls_cnt):
        bos = 1 if i == st.mpls_cnt - 1 else 0
        entry = (random.getrandbits(20) << 12) | (random.getrandbits(3) << 9) | (bos << 8) | random.getrandbits(8)
        pkt += entry.to_bytes(4, "big")
        ends.append(len(pkt))

    if st.l3 == "ipv4":
        hdr = bytearray(rand_bytes(st.ihl * 4))
        hdr[0] = 0x40 | st.ihl
        hdr[9] = st.l4
        pkt += bytes(hdr)
        ends.append(len(pkt))
    elif st.l3 == "ipv6":
        next_hdrs = list(st.ext_types) + [st.l4]
        hdr = bytearray(rand_bytes(40))
        hdr[0] = 0x60 | (hdr[0] & 0x0F)
        hdr[6] = next_hdrs[0]
        pkt += bytes(hdr)
        ends.append(len(pkt))
        for i, ext_len in enumerate(st.ext_lens):
            real_len = 0 if ext_len > 2 else ext_len
            ext = bytearray(rand_bytes((real_len + 1) * 8))
            ext[0] = next_hdrs[i + 1]
            ext[1] = ext_len
            pkt += bytes(ext)
            ends.append(len(pkt))
    else:
        # After MPLS, the first 4 bits must not look like an IP version
        first = random.choice([0x00, 0x10, 0x50, 0xF0]) | random.getrandbits(4)
        pkt += bytes([first])

    if st.l3 != "other":
        if st.l4 == IP_PROTO_TCP:
            hdr = bytearray(rand_bytes(st.tcp_data_offset * 4))
            hdr[12] = (st.tcp_data_offset << 4) | (hdr[12] & 0x0F)
            pkt += bytes(hdr)
            ends.append(len(pkt))
        elif st.l4 == IP_PROTO_UDP:
            pkt += rand_bytes(8)
            ends.append(len(pkt))

    pkt += rand_bytes(random.randint(0, payload_max))
    if len(pkt) < min_len:
        pkt += rand_bytes(min_len - len(pkt))
    return pkt, ends


def all_stacks(variants: int = 4) -> List[Stack]:
    """Every combination of the header protocols, each in several variants.

    The variants change the VLAN TPID, the MPLS ethertype, the IPv6 extension
    header type, IHL and the TCP data offset. Each variant uses another value
    at each position, so all values are used at all positions.
    """
    stacks = []
    l3_l4 = [("other", 0, 0)]
    for l4 in [IP_PROTO_TCP, IP_PROTO_UDP, None]:
        l3_l4.append(("ipv4", 0, l4))
        for ext_cnt in range(MAX_IPV6_EXT + 1):
            l3_l4.append(("ipv6", ext_cnt, l4))

    for vlan_cnt, mpls_cnt, (l3, ext_cnt, l4) in itertools.product(range(MAX_VLAN + 1), range(MAX_MPLS + 1), l3_l4):
        for v in range(variants):
            ext_types = tuple(IPV6_EXT_TYPES[(v + i) % len(IPV6_EXT_TYPES)] for i in range(ext_cnt))
            stacks.append(Stack(
                tpids=tuple(VLAN_TPIDS[(v + i) % len(VLAN_TPIDS)] for i in range(vlan_cnt)),
                mpls_cnt=mpls_cnt,
                mpls_type=ETH_TYPE_MPLS[v % len(ETH_TYPE_MPLS)],
                l3=l3,
                other_type=OTHER_ETH_TYPES[v % len(OTHER_ETH_TYPES)],
                ihl=[5, 6, 15, 7][v % 4],
                ext_types=ext_types,
                ext_lens=tuple(0 if t == IPV6_EXT_FRAGMENT else (v + i) % 3 for i, t in enumerate(ext_types)),
                l4=l4 if l4 is not None else (IPV4_PROTO_OTHER if l3 == "ipv4" else IPV6_PROTO_OTHER)[v % 4],
                tcp_data_offset=[5, 8, 15, 6][v % 4],
            ))
    return stacks


def cut_lengths(pkt_len: int, ends: List[int], min_len: int = 60) -> List[int]:
    """Packet lengths that cut the packet inside or at the end of a header.

    A cut at end-1 removes the last byte of a header. A cut at end removes
    everything after the header, which also removes the byte after an MPLS
    entry. Lengths below min_len are not used, a real link pads such frames.
    """
    lengths = set()
    for end in ends:
        for cut in (end - 1, end):
            if min_len <= cut < pkt_len:
                lengths.add(cut)
    return sorted(lengths)


def random_stack(malformed: bool = False) -> Stack:
    l3 = random.choice(["ipv4", "ipv4", "ipv6", "ipv6", "other"])
    ext_types = tuple(random.choice(IPV6_EXT_TYPES) for _ in range(random.choice([0, 0, 1, 2, 3]))) if l3 == "ipv6" else ()
    ext_lens = []
    for t in ext_types:
        ext_len = 0 if t == IPV6_EXT_FRAGMENT else random.choice([0, 0, 1, 2])
        # A malformed hdr_ext_len announces more bytes than the header has
        if malformed and random.random() < 0.5:
            ext_len = random.choice([255, 250, random.randint(128, 255)])
        ext_lens.append(ext_len)
    return Stack(
        tpids=tuple(random.choice(VLAN_TPIDS) for _ in range(random.choice([0, 0, 1, 1, 2, 3]))),
        mpls_cnt=random.choice([0, 0, 0, 1, 2, 3]),
        mpls_type=random.choice(ETH_TYPE_MPLS),
        l3=l3,
        other_type=random.choice(OTHER_ETH_TYPES),
        ihl=random.choice([5, 5, 5, 6, 7, 15]),
        ext_types=ext_types,
        ext_lens=tuple(ext_lens),
        l4=random.choice([IP_PROTO_TCP, IP_PROTO_UDP] + (IPV4_PROTO_OTHER if l3 == "ipv4" else IPV6_PROTO_OTHER)),
        tcp_data_offset=random.choice([5, 5, 5, 6, 8, 15]),
    )


def build_packet(min_len: int = 60, max_len: int = 512, malformed: bool = False) -> bytes:
    """Build one random packet with a random stack of headers."""
    pkt, _ = build_stack(random_stack(malformed), min_len, payload_max=random.randint(0, max_len))
    return pkt


def malform_packet(pkt: bytes, min_len: int = 60) -> bytes:
    """Change random bytes in the headers and cut the packet short.

    The length stays at least min_len, so the packet looks like a padded
    minimum-size frame on a real link.
    """
    data = bytearray(pkt)
    for _ in range(random.randint(1, 3)):
        pos = random.randint(12, min(len(data) - 1, 100))
        data[pos] = random.getrandbits(8)
    new_len = random.randint(min_len, max(min_len, min(len(data), 140)))
    return bytes(data[:new_len])
