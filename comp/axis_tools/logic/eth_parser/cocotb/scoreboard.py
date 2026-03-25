# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Scoreboard module for AXIS_ETH_PARSER verification.

This module contains the dataclass for header extraction results
and the comparison function for scoreboard verification.
"""

from dataclasses import dataclass
from typing import Tuple


@dataclass(eq=False)
class AxisEthParserResult:
    """Dataclass for storing expected/actual header extraction results.

    Attributes:
        eth_dst_mac: Destination MAC address (6 bytes as integer)
        eth_src_mac: Source MAC address (6 bytes as integer)
        eth_ethertype: Ethernet type field (2 bytes as integer)
        eth_vld: Ethernet header valid flag
        eth_offset: Offset to Ethernet header
        vlan_tci: VLAN TCI (16 bits) - PCP (3) + DEI (1) + VID (12)
        vlan_ethertype: Encapsulated protocol ethertype following VLAN header
        vlan_vld: VLAN header valid flag
        vlan_offset: Offset to VLAN header
        ipv4_version: IP version (4 bits)
        ipv4_ihl: IP header length (4 bits)
        ipv4_tos: Type of Service field (8 bits) - DSCP (bits 7-2) + ECN (bits 1-0)
        ipv4_total_length: Total length field
        ipv4_identification: Identification field
        ipv4_flags: Flags field (3 bits)
        ipv4_fragment_offset: Fragment offset (13 bits)
        ipv4_ttl: TTL field
        ipv4_protocol: Protocol field
        ipv4_header_checksum: Header checksum
        ipv4_src_ip: Source IP address
        ipv4_dst_ip: Destination IP address
        ipv4_vld: IPv4 header valid flag
        ipv4_offset: Offset to IPv4 header
        tcp_src_port: Source port
        tcp_dst_port: Destination port
        tcp_seq_num: Sequence number
        tcp_ack_num: Acknowledgment number
        tcp_data_offset: Data offset (4 bits)
        tcp_reserved: Reserved bits (3 bits)
        tcp_flags: Flags (9 bits)
        tcp_window: Window size
        tcp_checksum: Checksum
        tcp_urgent_ptr: Urgent pointer
        tcp_vld: TCP header valid flag
        tcp_offset: Offset to TCP header
    """
    eth_dst_mac: int = 0
    eth_src_mac: int = 0
    eth_ethertype: int = 0
    eth_vld: int = 0
    eth_offset: int = 0

    vlan_tci: int = 0
    vlan_ethertype: int = 0
    vlan_vld: int = 0
    vlan_offset: int = 0

    ipv4_version: int = 0
    ipv4_ihl: int = 0
    ipv4_tos: int = 0
    ipv4_total_length: int = 0
    ipv4_identification: int = 0
    ipv4_flags: int = 0
    ipv4_fragment_offset: int = 0
    ipv4_ttl: int = 0
    ipv4_protocol: int = 0
    ipv4_header_checksum: int = 0
    ipv4_src_ip: int = 0
    ipv4_dst_ip: int = 0
    ipv4_vld: int = 0
    ipv4_offset: int = 0

    tcp_src_port: int = 0
    tcp_dst_port: int = 0
    tcp_seq_num: int = 0
    tcp_ack_num: int = 0
    tcp_data_offset: int = 0
    tcp_reserved: int = 0
    tcp_flags: int = 0
    tcp_window: int = 0
    tcp_checksum: int = 0
    tcp_urgent_ptr: int = 0
    tcp_vld: int = 0
    tcp_offset: int = 0

    packet_num: int = 0  # Packet number for debugging
    packet_bytes: bytes = b''  # Original packet bytes for debugging

    def __eq__(self, other: 'AxisEthParserResult') -> bool:
        """Check equality using compare_headers function."""
        if not isinstance(other, AxisEthParserResult):
            return False
        match, _ = compare_headers(self, other)
        return match


def _fmt_val(val, is_mac=False, is_ip=False, is_vlan=False, is_offset=False, is_ethertype=False) -> str:
    """Format value for display."""
    if is_mac:
        return f"0x{val:012X}" if isinstance(val, int) else str(val)
    if is_ip:
        return f"0x{val:08X}" if isinstance(val, int) else str(val)
    if is_vlan:
        return f"0x{val:04X}" if isinstance(val, int) else str(val)
    if is_ethertype:
        return f"0x{val:04X}" if isinstance(val, int) else str(val)
    if is_offset:
        return str(val) if isinstance(val, int) else str(val)  # Decimal for offsets
    return str(val)


def _fmt_vld(val) -> str:
    """Format valid flag for display."""
    return "1" if val else "0"


def _format_row(field: str, exp_val, act_val, match: bool) -> str:
    """Format a single row of the comparison table.

    Args:
        field: Field name
        exp_val: Expected value
        act_val: Actual value
        match: True if values match

    Returns:
        Formatted table row string
    """
    is_mac = 'mac' in field.lower()
    is_ip = 'ip' in field.lower()
    is_vlan = 'vlan' in field.lower()
    is_offset = 'offset' in field.lower()
    is_ethertype = 'ethertype' in field.lower()

    exp_str = _fmt_val(exp_val, is_mac, is_ip, is_vlan, is_offset, is_ethertype)
    act_str = _fmt_val(act_val, is_mac, is_ip, is_vlan, is_offset, is_ethertype)

    marker = " " if match else "X"

    # Format: # + space + marker + space + field(18) + 2 spaces + exp(18) + 2 spaces + act(18) + space + #
    return f"# {marker} {field:<18}  {exp_str:>18}  {act_str:>18}   #"


def _format_packet_bytes(packet_bytes: bytes, label: str) -> str:
    """Format packet bytes for display, 16 bytes per line.

    Args:
        packet_bytes: Raw packet bytes
        label: Label to display before the bytes

    Returns:
        Formatted string with bytes nicely aligned
    """
    lines = [f"{label}:"]
    for i in range(0, len(packet_bytes), 16):
        chunk = packet_bytes[i:i+16]
        hex_str = ' '.join(f'{b:02X}' for b in chunk)
        ascii_str = ''.join(chr(b) if 32 <= b < 127 else '.' for b in chunk)
        lines.append(f"  {i:04X}: {hex_str:<48} {ascii_str}")
    return '\n'.join(lines)


def compare_headers(expected: AxisEthParserResult, actual: AxisEthParserResult) -> Tuple[bool, str]:
    """Compare two AxisEthParserResult objects.

    This function compares expected and actual header extraction results
    field by field. Only fields with valid flags set in the expected
    result are compared.

    Args:
        expected: Expected header values from the reference model
        actual: Actual header values from the DUT

    Returns:
        Tuple of (match_ok, error_message):
            - match_ok: True if all compared fields match
            - error_message: Empty string if match, otherwise contains
              detailed error description in table format
    """

    rows = []
    has_error = False

    # 1. Packet number first
    match = expected.packet_num == actual.packet_num
    has_error |= not match
    rows.append(_format_row("packet_num", expected.packet_num, actual.packet_num, match))

    # 2. All valid flags (even if not present in packet)
    match = expected.eth_vld == actual.eth_vld
    has_error |= not match
    rows.append(_format_row("eth_vld", _fmt_vld(expected.eth_vld), _fmt_vld(actual.eth_vld), match))

    match = expected.vlan_vld == actual.vlan_vld
    has_error |= not match
    rows.append(_format_row("vlan_vld", _fmt_vld(expected.vlan_vld), _fmt_vld(actual.vlan_vld), match))

    match = expected.ipv4_vld == actual.ipv4_vld
    has_error |= not match
    rows.append(_format_row("ipv4_vld", _fmt_vld(expected.ipv4_vld), _fmt_vld(actual.ipv4_vld), match))

    match = expected.tcp_vld == actual.tcp_vld
    has_error |= not match
    rows.append(_format_row("tcp_vld", _fmt_vld(expected.tcp_vld), _fmt_vld(actual.tcp_vld), match))

    # 3. Ethernet fields if valid
    if expected.eth_vld:
        match = expected.eth_dst_mac == actual.eth_dst_mac
        has_error |= not match
        rows.append(_format_row("eth_dst_mac", expected.eth_dst_mac, actual.eth_dst_mac, match))

        match = expected.eth_src_mac == actual.eth_src_mac
        has_error |= not match
        rows.append(_format_row("eth_src_mac", expected.eth_src_mac, actual.eth_src_mac, match))

        match = expected.eth_ethertype == actual.eth_ethertype
        has_error |= not match
        rows.append(_format_row("eth_ethertype", expected.eth_ethertype, actual.eth_ethertype, match))

        match = expected.eth_offset == actual.eth_offset
        has_error |= not match
        rows.append(_format_row("eth_offset", expected.eth_offset, actual.eth_offset, match))

    # 4. VLAN fields if valid
    if expected.vlan_vld:
        match = expected.vlan_tci == actual.vlan_tci
        has_error |= not match
        rows.append(_format_row("vlan_tci", expected.vlan_tci, actual.vlan_tci, match))

        match = expected.vlan_ethertype == actual.vlan_ethertype
        has_error |= not match
        rows.append(_format_row("vlan_ethertype", expected.vlan_ethertype, actual.vlan_ethertype, match))

        match = expected.vlan_offset == actual.vlan_offset
        has_error |= not match
        rows.append(_format_row("vlan_offset", expected.vlan_offset, actual.vlan_offset, match))

    # 5. IPv4 fields if valid
    if expected.ipv4_vld:
        match = expected.ipv4_version == actual.ipv4_version
        has_error |= not match
        rows.append(_format_row("ipv4_version", expected.ipv4_version, actual.ipv4_version, match))

        match = expected.ipv4_ihl == actual.ipv4_ihl
        has_error |= not match
        rows.append(_format_row("ipv4_ihl", expected.ipv4_ihl, actual.ipv4_ihl, match))

        match = expected.ipv4_tos == actual.ipv4_tos
        has_error |= not match
        rows.append(_format_row("ipv4_tos", expected.ipv4_tos, actual.ipv4_tos, match))

        match = expected.ipv4_total_length == actual.ipv4_total_length
        has_error |= not match
        rows.append(_format_row("ipv4_total_len", expected.ipv4_total_length, actual.ipv4_total_length, match))

        match = expected.ipv4_identification == actual.ipv4_identification
        has_error |= not match
        rows.append(_format_row("ipv4_ident", expected.ipv4_identification, actual.ipv4_identification, match))

        match = expected.ipv4_ttl == actual.ipv4_ttl
        has_error |= not match
        rows.append(_format_row("ipv4_ttl", expected.ipv4_ttl, actual.ipv4_ttl, match))

        match = expected.ipv4_protocol == actual.ipv4_protocol
        has_error |= not match
        rows.append(_format_row("ipv4_proto", expected.ipv4_protocol, actual.ipv4_protocol, match))

        match = expected.ipv4_header_checksum == actual.ipv4_header_checksum
        has_error |= not match
        rows.append(_format_row("ipv4_checksum", expected.ipv4_header_checksum, actual.ipv4_header_checksum, match))

        match = expected.ipv4_src_ip == actual.ipv4_src_ip
        has_error |= not match
        rows.append(_format_row("ipv4_src_ip", expected.ipv4_src_ip, actual.ipv4_src_ip, match))

        match = expected.ipv4_dst_ip == actual.ipv4_dst_ip
        has_error |= not match
        rows.append(_format_row("ipv4_dst_ip", expected.ipv4_dst_ip, actual.ipv4_dst_ip, match))

        match = expected.ipv4_offset == actual.ipv4_offset
        has_error |= not match
        rows.append(_format_row("ipv4_offset", expected.ipv4_offset, actual.ipv4_offset, match))

    # 6. TCP fields if valid
    if expected.tcp_vld:
        match = expected.tcp_src_port == actual.tcp_src_port
        has_error |= not match
        rows.append(_format_row("tcp_src_port", expected.tcp_src_port, actual.tcp_src_port, match))

        match = expected.tcp_dst_port == actual.tcp_dst_port
        has_error |= not match
        rows.append(_format_row("tcp_dst_port", expected.tcp_dst_port, actual.tcp_dst_port, match))

        match = expected.tcp_seq_num == actual.tcp_seq_num
        has_error |= not match
        rows.append(_format_row("tcp_seq_num", expected.tcp_seq_num, actual.tcp_seq_num, match))

        match = expected.tcp_ack_num == actual.tcp_ack_num
        has_error |= not match
        rows.append(_format_row("tcp_ack_num", expected.tcp_ack_num, actual.tcp_ack_num, match))

        match = expected.tcp_flags == actual.tcp_flags
        has_error |= not match
        rows.append(_format_row("tcp_flags", expected.tcp_flags, actual.tcp_flags, match))

        match = expected.tcp_window == actual.tcp_window
        has_error |= not match
        rows.append(_format_row("tcp_window", expected.tcp_window, actual.tcp_window, match))

        match = expected.tcp_offset == actual.tcp_offset
        has_error |= not match
        rows.append(_format_row("tcp_offset", expected.tcp_offset, actual.tcp_offset, match))

    # Build formatted table - all lines exactly 66 chars: # + 64 chars + #
    lines = []
    lines.append("")
    lines.append("#" + "=" * 64 + "#")
    lines.append("#" + " " * 20 + "HEADER COMPARISON" + " " * 27 + "#")
    lines.append("#" + "=" * 64 + "#")
    lines.append("#    Field                  Expected            Actual           #")
    lines.append("#" + "-" * 64 + "#")
    lines.extend(rows)
    lines.append("#" + "=" * 64 + "#")
    lines.append("#  X = mismatch" + " " * 50 + "#")
    lines.append("#" + "=" * 64 + "#")
    lines.append("")

    msg = "\n".join(lines)
    msg += "\n" + _format_packet_bytes(expected.packet_bytes, "Packet bytes (Expected)") + "\n"
    msg += "\n" + _format_packet_bytes(actual.packet_bytes, "Packet bytes (Actual/DUT)") + "\n"

    return not has_error, msg
