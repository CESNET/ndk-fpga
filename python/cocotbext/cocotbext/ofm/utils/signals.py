# signals.py: Cocotbext signal utilities
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <Ondrej.Schwarz@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

async def await_signal_sync(clk_re, signal, value: int = 1) -> None:
    """Synchronously waits until the value of the passed signal becomes passed value.

    Note:
        If the value of the signal is already set to passed value, function returns immediately.

    Args:
        signal: signal that is to be awaited, must be signal from the cocotb.bus class.
        value: value that is to be awaited.
        clk_re: RisingEdge object.

    """

    while signal.value != value:
        await clk_re


def get_signal_value_in_bytes(signal, big_endian: bool = False) -> bytes:
    """Get value of a OUT signals in bytes.

    Args:
        signal: cocotb.bus signal that is to be read.
        big_endian: using which endian are the data to be interpreted (little endian by default)

    Returns:
        Signal value in bytes.

    """

    sig_val = signal.value
    sig_val.big_endian = big_endian

    return sig_val.buff
