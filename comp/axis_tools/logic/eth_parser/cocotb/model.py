# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Reference model of AXIS_ETH_PARSER_GEN.

The model works like the parser pipeline. Each stage reads the header only
when the previous headers announce its protocol. Otherwise it passes the
announced protocol and offset to the next stage.
"""

from dataclasses import dataclass, field
from typing import List

PROTO_NONE = 0
PROTO_ETH = 1
PROTO_VLAN = 2
PROTO_IPV4 = 3
PROTO_TCP = 4
PROTO_UDP = 5
PROTO_IPV6 = 6
PROTO_IPV6EXT = 7
PROTO_MPLS = 8

PROTO_NAMES = {
    PROTO_NONE: "NONE",
    PROTO_ETH: "ETH",
    PROTO_VLAN: "VLAN",
    PROTO_IPV4: "IPV4",
    PROTO_TCP: "TCP",
    PROTO_UDP: "UDP",
    PROTO_IPV6: "IPV6",
    PROTO_IPV6EXT: "IPV6EXT",
    PROTO_MPLS: "MPLS",
}

# Number of header bytes that a stage reads (get_extract_bytes in the VHDL package)
EXTRACT_BYTES = {
    PROTO_ETH: 14,
    PROTO_VLAN: 4,
    PROTO_IPV4: 20,
    PROTO_TCP: 20,
    PROTO_UDP: 8,
    PROTO_IPV6: 40,
    PROTO_IPV6EXT: 8,
    PROTO_MPLS: 5,
}

ETHERTYPE_TO_PROTO = {
    0x8100: PROTO_VLAN,
    0x88A8: PROTO_VLAN,
    0x9100: PROTO_VLAN,
    0x0800: PROTO_IPV4,
    0x86DD: PROTO_IPV6,
    0x8847: PROTO_MPLS,
    0x8848: PROTO_MPLS,
}

IP_PROTO_TO_PROTO = {
    6: PROTO_TCP,
    17: PROTO_UDP,
}

IPV6_NEXT_TO_PROTO = {
    **IP_PROTO_TO_PROTO,
    0: PROTO_IPV6EXT,
    43: PROTO_IPV6EXT,
    44: PROTO_IPV6EXT,
    60: PROTO_IPV6EXT,
}


@dataclass
class StageResult:
    """Header of one parser stage."""
    found: bool = False
    offset: int = 0
    data: bytes = b""


@dataclass
class ParserResult:
    """Headers of all parser stages for one packet."""
    stages: List[StageResult] = field(default_factory=list)
    packet: bytes = b""


def next_proto(proto: int, d: bytes) -> int:
    """Protocol of the next header (get_next_proto in the VHDL package)."""
    if proto == PROTO_ETH:
        return ETHERTYPE_TO_PROTO.get(int.from_bytes(d[12:14], "big"), PROTO_NONE)
    if proto == PROTO_VLAN:
        return ETHERTYPE_TO_PROTO.get(int.from_bytes(d[2:4], "big"), PROTO_NONE)
    if proto == PROTO_IPV4:
        return IP_PROTO_TO_PROTO.get(d[9], PROTO_NONE)
    if proto == PROTO_IPV6:
        return IPV6_NEXT_TO_PROTO.get(d[6], PROTO_NONE)
    if proto == PROTO_IPV6EXT:
        return IPV6_NEXT_TO_PROTO.get(d[0], PROTO_NONE)
    if proto == PROTO_MPLS:
        if (d[2] & 1) == 0:
            return PROTO_MPLS
        return {4: PROTO_IPV4, 6: PROTO_IPV6}.get(d[4] >> 4, PROTO_NONE)
    return PROTO_NONE


def hdr_len(proto: int, d: bytes) -> int:
    """Header length in bytes (get_hdr_len in the VHDL package)."""
    if proto == PROTO_IPV4:
        ihl = d[0] & 0xF
        return 20 if ihl < 5 else ihl * 4
    if proto == PROTO_IPV6EXT:
        return (d[1] + 1) * 8
    if proto == PROTO_MPLS:
        return 4
    return EXTRACT_BYTES[proto]


class ParserModel:
    """Model of the parser for one protocol list."""

    def __init__(self, protocols: List[int], pkt_mtu: int):
        self.protocols = protocols
        self.pkt_mtu = pkt_mtu

    def parse(self, pkt: bytes) -> ParserResult:
        result = ParserResult(packet=pkt)
        cur_proto = PROTO_ETH
        cur_offset = 0
        for proto in self.protocols:
            stage = StageResult(offset=cur_offset)
            if cur_proto == proto:
                nbytes = EXTRACT_BYTES[proto]
                d = pkt[cur_offset:cur_offset + nbytes]
                if len(d) == nbytes:
                    stage.found = True
                    stage.data = d
                    cur_proto = next_proto(proto, d)
                    if cur_offset + hdr_len(proto, d) > self.pkt_mtu:
                        cur_proto = PROTO_NONE
                    else:
                        cur_offset += hdr_len(proto, d)
                else:
                    cur_proto = PROTO_NONE
            result.stages.append(stage)
        return result
