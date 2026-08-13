# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from dataclasses import dataclass, field
from typing import Optional
from enum import Enum

from cocotb.triggers import Event
from cocotbext.ofm.base.transaction import Transaction


class AvalonMMResponseValue(Enum):
    OKAY        = 0
    RESERVED    = 1
    SLVERR      = 2
    DECODEERROR = 3


@dataclass
class AvalonMMTransaction(Transaction):
    pass


@dataclass
class AvalonMMResponseTransaction(AvalonMMTransaction):
    response : Optional[int] = None


@dataclass
class AvalonMMWriteResponseTransaction(AvalonMMResponseTransaction):
    pass


@dataclass
class AvalonMMReadResponseTransaction(AvalonMMResponseTransaction):
    data     : bytes = field(default_factory=list)


@dataclass
class AvalonMMRequestTransaction(AvalonMMTransaction):
    address     : int = field(default_factory=int)
    burst_count : Optional[int] = None
    byte_enable : Optional[int] = None


@dataclass
class AvalonMMReadRequestTransaction(AvalonMMRequestTransaction):
    event    : Event = None
    response : AvalonMMReadResponseTransaction = None

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.response = AvalonMMReadResponseTransaction()


@dataclass
class AvalonMMWriteRequestTransaction(AvalonMMRequestTransaction):
    data     : bytes = field(default_factory=bytes)
    response : AvalonMMWriteResponseTransaction = None

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.response = AvalonMMWriteResponseTransaction()
