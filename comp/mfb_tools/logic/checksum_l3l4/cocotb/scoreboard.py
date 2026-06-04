# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Scoreboard module for MFB_CHECKSUM_L3L4 verification.

This module contains the dataclass for checksum results
and the comparison function for scoreboard verification.
"""

from dataclasses import dataclass
from typing import Tuple

from cocotbext.ofm.utils.hex_formatter import format_bytes


@dataclass(eq=False)
class MfbChecksumL3L4Result:
    """Dataclass for storing expected/actual checksum results.

    Attributes:
        l3_csum: L3 checksum value
        l3_csum_ok: L3 checksum OK flag
        l3_csum_en: L3 checksum enable flag
        l4_csum: L4 checksum value
        l4_csum_ok: L4 checksum OK flag
        l4_csum_en: L4 checksum enable flag
        packet_num: Packet number for debugging
        packet_bytes: Original packet bytes for debugging
    """
    l3_csum: int = 0
    l3_csum_ok: int = 0
    l3_csum_en: int = 0
    l4_csum: int = 0
    l4_csum_ok: int = 0
    l4_csum_en: int = 0

    packet_num: int = 0  # Packet number for debugging
    packet_bytes: bytes = b''  # Original packet bytes for debugging

    def __eq__(self, other: 'MfbChecksumL3L4Result') -> bool:
        """Check equality using compare_checksums function."""
        if not isinstance(other, MfbChecksumL3L4Result):
            return False
        match, _ = compare_checksums(self, other)
        return match


def _fmt_val(val, is_checksum=False) -> str:
    """Format value for display."""
    if is_checksum:
        return f"0x{val:04X}" if isinstance(val, int) else str(val)
    return str(val)


def _fmt_flag(val) -> str:
    """Format flag for display."""
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
    is_checksum = 'csum' in field.lower()

    exp_str = _fmt_val(exp_val, is_checksum)
    act_str = _fmt_val(act_val, is_checksum)

    marker = " " if match else "X"
    # Format: # + space + marker + space + field(18) + 2 spaces + exp(18) + 2 spaces + act(18) + space + #
    return f"# {marker} {field:<18}  {exp_str:>18}  {act_str:>18}   #"


def compare_checksums(expected: MfbChecksumL3L4Result, actual: MfbChecksumL3L4Result) -> Tuple[bool, str]:
    """Compare two MfbChecksumL3L4Result objects.

    This function compares expected and actual checksum results
    field by field.

    Args:
        expected: Expected checksum values from the reference model
        actual: Actual checksum values from the DUT

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

    # 2. L3 checksum enable flag
    match = expected.l3_csum_en == actual.l3_csum_en
    has_error |= not match
    rows.append(_format_row("l3_csum_en", _fmt_flag(expected.l3_csum_en), _fmt_flag(actual.l3_csum_en), match))

    # 3. L4 checksum enable flag
    match = expected.l4_csum_en == actual.l4_csum_en
    has_error |= not match
    rows.append(_format_row("l4_csum_en", _fmt_flag(expected.l4_csum_en), _fmt_flag(actual.l4_csum_en), match))

    # 4. L3 checksum fields if enabled
    if expected.l3_csum_en:
        match = expected.l3_csum == actual.l3_csum
        has_error |= not match
        rows.append(_format_row("l3_csum", expected.l3_csum, actual.l3_csum, match))

        match = expected.l3_csum_ok == actual.l3_csum_ok
        has_error |= not match
        rows.append(_format_row("l3_csum_ok", _fmt_flag(expected.l3_csum_ok), _fmt_flag(actual.l3_csum_ok), match))

    # 5. L4 checksum fields if enabled
    if expected.l4_csum_en:
        match = expected.l4_csum == actual.l4_csum
        has_error |= not match
        rows.append(_format_row("l4_csum", expected.l4_csum, actual.l4_csum, match))

        match = expected.l4_csum_ok == actual.l4_csum_ok
        has_error |= not match
        rows.append(_format_row("l4_csum_ok", _fmt_flag(expected.l4_csum_ok), _fmt_flag(actual.l4_csum_ok), match))

    # Build formatted table - all lines exactly 66 chars: # + 64 chars + #
    lines = []
    lines.append("")
    lines.append("#" + "=" * 64 + "#")
    lines.append("#" + " " * 18 + "CHECKSUM COMPARISON" + " " * 27 + "#")
    lines.append("#" + "=" * 64 + "#")
    lines.append("#    Field                  Expected            Actual           #")
    lines.append("#" + "-" * 64 + "#")
    lines.extend(rows)
    lines.append("#" + "=" * 64 + "#")
    lines.append("#  X = mismatch" + " " * 50 + "#")
    lines.append("#" + "=" * 64 + "#")
    lines.append("")

    msg = "\n".join(lines)
    msg += "\n" + format_bytes(expected.packet_bytes, label="Packet bytes (Expected)", max_bytes=256) + "\n"
    msg += "\n" + format_bytes(actual.packet_bytes, label="Packet bytes (Actual/DUT)", max_bytes=256) + "\n"

    return not has_error, msg
