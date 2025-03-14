# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <ondrejschwarz@cesnet.cz>


from dataclasses import dataclass
from enum import Enum
from cocotbext.ofm.base.transaction import Transaction


class MiTransactionType(Enum):
    Request  = 0
    Response = 1


@dataclass
class MiBaseTransaction(Transaction):
    """Base class for MI Transactions with configurable data items"""


@dataclass
class MiRequestTransaction(MiBaseTransaction):
    """Transaction for MI Request driver."""
    trans_type : MiTransactionType = None
    addr       : int = 0
    data       : bytes = b""
    data_len   : int = 0


@dataclass
class MiResponseTransaction(MiBaseTransaction):
    """Transaction for MI Response driver."""
    trans_type : MiTransactionType = None
    data       : bytes = b""


@dataclass
class MiTransaction(MiRequestTransaction):
    """Full MI transaction for monitor and test."""
    be: int = 0
