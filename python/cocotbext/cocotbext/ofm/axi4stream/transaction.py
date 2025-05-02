# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from dataclasses import dataclass
from cocotbext.ofm.base.transaction import Transaction


@dataclass
class Axi4StreamBaseTransaction(Transaction):
    """
    Base class for Axi4Stream transactions.
    """


@dataclass
class Axi4StreamTransaction(Axi4StreamBaseTransaction):
    """
    Axi4Stream transaction with TDATA and TUSER.
    """
    TDATA : bytes = b''
    TUSER : bytes = b''


@dataclass
class Axi4StreamTransactionWithSelect(Axi4StreamTransaction):
    """
    Axi4Stream transaction with TDATA, TUSER and selector SEL.
    """
    SEL: int = 0
