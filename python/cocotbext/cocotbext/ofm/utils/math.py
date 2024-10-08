# math.py: OFM Math Math Library
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
