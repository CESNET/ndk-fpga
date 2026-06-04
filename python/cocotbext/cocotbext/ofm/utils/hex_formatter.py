# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>

"""Hex formatting utilities for transaction data display.

Provides configurable hex dump functionality for displaying transaction data
in cocotb verification tests. Replaces cocotb.utils.hexdump() with cleaner
output format suitable for NDK-FPGA verifications.

Example:
    >>> from cocotbext.ofm.utils.hex_formatter import format_bytes
    >>> format_bytes(b'\x01\x02\x03\x04', label="TDATA")
    'TDATA:\\n  0000: 01 02 03 04'
"""

from typing import Union, Optional
from dataclasses import dataclass


@dataclass
class HexFormatConfig:
    """Configuration for hex formatting.

    Attributes:
        bytes_per_line: Number of bytes per line (default: 16).
        group_size: Basic grouping with single space (default: 1). 0 = no grouping.
        super_group_size: Super grouping with double space (default: 4). 0 = no super grouping.
    """
    bytes_per_line: int = 16
    group_size: int = 1
    super_group_size: int = 4


def _to_bytes(data: Union[bytes, bytearray, int]) -> bytes:
    """Convert data to bytes.

    Args:
        data: Input data (bytes, bytearray, or int).

    Returns:
        Data as bytes.

    Raises:
        TypeError: If data type is not supported.
        ValueError: If negative integer provided.
    """
    if isinstance(data, bytes):
        return data
    if isinstance(data, bytearray):
        return bytes(data)
    if isinstance(data, int):
        if data < 0:
            raise ValueError("Negative integers not supported")
        length = 1 if data == 0 else (data.bit_length() + 7) // 8
        return data.to_bytes(length, byteorder='big')
    raise TypeError(f"Expected bytes, bytearray, or int, got {type(data).__name__}")


def _format_hex_byte(byte: int) -> str:
    """Format single byte as uppercase hex.

    Args:
        byte: Byte value (0-255).

    Returns:
        Two-character uppercase hex string.
    """
    return f"{byte:02X}"


def _build_hex_string(chunk: bytes, cfg: HexFormatConfig) -> str:
    """Build hex string from chunk with grouping.

    Args:
        chunk: Bytes to format.
        cfg: Formatting configuration.

    Returns:
        Formatted hex string with separators.
    """
    parts = []
    for i, byte in enumerate(chunk):
        if i > 0:
            if cfg.super_group_size > 0 and i % cfg.super_group_size == 0:
                parts.append("  ")
            elif cfg.group_size > 0 and i % cfg.group_size == 0:
                parts.append(" ")
        parts.append(_format_hex_byte(byte))
    return ''.join(parts)


def _format_line(offset: int, chunk: bytes, cfg: HexFormatConfig) -> str:
    """Format a single line of hex output.

    Args:
        offset: Byte offset for address display.
        chunk: Bytes to format.
        cfg: Formatting configuration.

    Returns:
        Formatted line with address and hex values.
    """
    addr = f"{offset:04X}: "
    hex_str = _build_hex_string(chunk, cfg)
    return f"  {addr}{hex_str}"


def format_bytes(
    data: Union[bytes, bytearray, int],
    *,
    label: Optional[str] = None,
    max_bytes: Optional[int] = None,
    bytes_per_line: int = 16,
    group_size: int = 1,
    super_group_size: int = 4,
) -> str:
    """Format bytes data as hex string with two-level grouping.

    Args:
        data: Data to format (bytes, bytearray, or int).
        label: Optional label to prepend (e.g., "TDATA", "DATA").
        max_bytes: Maximum bytes to display. None = show all (default).
        bytes_per_line: Number of bytes per line (default: 16).
        group_size: Bytes per basic group (single space). 0 = no grouping.
        super_group_size: Bytes per super group (double space). 0 = no super grouping.

    Returns:
        Formatted hex string.

    Raises:
        TypeError: If data type is not supported.
        ValueError: If negative integer provided.

    Example:
        >>> format_bytes(b'\x01\x02\x03\x04', label="TDATA")
        'TDATA:\\n  0000: 01 02 03 04'

        >>> format_bytes(0xDEADBEEF, max_bytes=4)
        '  0000: DE AD BE EF'
    """
    data = _to_bytes(data)

    if not data:
        return f"{label}:" if label else ""

    cfg = HexFormatConfig(
        bytes_per_line=bytes_per_line,
        group_size=group_size,
        super_group_size=super_group_size,
    )

    # Calculate lines to display
    limit = max_bytes if max_bytes is not None else len(data)
    truncated = max_bytes is not None and len(data) > max_bytes

    lines = []
    if label:
        lines.append(f"{label}:")

    for offset in range(0, min(len(data), limit), bytes_per_line):
        chunk = data[offset:offset + bytes_per_line]
        lines.append(_format_line(offset, chunk, cfg))

    if truncated:
        lines.append(f"  ... ({len(data) - max_bytes} more bytes)")

    return '\n'.join(lines) if lines else ""


def format_hex_short(
    data: Union[bytes, bytearray, int],
    *,
    max_bytes: Optional[int] = None,
    label: Optional[str] = None,
) -> str:
    """Format bytes as compact single-line hex string.

    Args:
        data: Data to format.
        max_bytes: Maximum bytes to show. None = show all (default).
        label: Optional label to prepend.

    Returns:
        Compact single-line hex string.

    Example:
        >>> format_hex_short(b'\x01\x02\x03\x04', label="HDR")
        'HDR: 01020304'
    """
    data = _to_bytes(data)

    if not data:
        return f"{label}:" if label else ""

    truncated = max_bytes is not None and len(data) > max_bytes
    limit = max_bytes if truncated else len(data)

    hex_str = ''.join(_format_hex_byte(b) for b in data[:limit])

    if truncated:
        hex_str += f"... ({len(data) - max_bytes} more bytes)"

    return f"{label}: {hex_str}" if label else hex_str


__all__ = ['format_bytes', 'format_hex_short', 'HexFormatConfig']
