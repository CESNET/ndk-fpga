# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2024-2026 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#            Ondřej Schwarz <ondrejschwarz@cesnet.cz>

from dataclasses import dataclass
from random import randint


class BaseTransaction():
    """Base class for transactions"""


class IdleTransaction(BaseTransaction):
    """Transaction representing bus idling (no valid data on the bus).

    Drivers insert idle transactions between data transactions to model
    gaps in the traffic (deasserted SRC_RDY/TVALID etc.). The ``length``
    attribute expresses the duration of the gap in the bus's smallest
    transferable unit — e.g. one byte on the MFB bus, one item on the MVB
    bus, or one word (clock cycle) on common buses.

    Args:
        length: Duration of the idle gap in bus-specific units.
    """
    def __init__(self, length: int = 1):
        self.length = length

    def __len__(self):
        return self.length


class IdleTransactionFactory:
    """Factory producing idle transactions with a random length.

    Used by drivers to generate idle gaps of varying duration between
    data transactions. The length of each produced idle transaction is
    drawn uniformly at random from the interval
    [``min_length``, ``max_length``].

    Args:
        min_length: Minimum idle gap length (inclusive).
        max_length: Maximum idle gap length (inclusive).
    """
    def __init__(self, min_length: int = 1, max_length: int = 1024):
        self._min_length = min_length
        self._max_length = max_length

    def make(self) -> IdleTransaction:
        return IdleTransaction(randint(self._min_length, self._max_length))


@dataclass
class Transaction(BaseTransaction):
    """Transactions with real data to be written into bus"""


DataTransaction = Transaction
