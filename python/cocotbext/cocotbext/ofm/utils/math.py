# math.py: NDK-FPGA Math Library
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <Ondrej.Schwarz@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

def ceildiv(bus_width: int, transaction_len: int) -> int:
    """Calculates to how many transmission must the transaction be divided.

    Args:
        bus_width: width of the bus that is the transaction intended for.
        transaction_len: lenght of the transaction that is to be divided.

    Returns:
        Number of transmissions needed to send the whole transaction.

    """

    return (transaction_len + (bus_width - 1)) // bus_width


def numberOfSetBits(i):
    """
    Counts the number of bits that are set to a logical 1 in an integer.
    """
    i = i - ((i >> 1) & 0x55555555)
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333)
    return (((i + (i >> 4) & 0xF0F0F0F) * 0x1010101) & 0xFFFFFFFF) >> 24


def bitmask(bits):
    """
    Returns a bitmask as an integer of a specified length.
    """
    return (2**bits) - 1
