# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>

from dataclasses import dataclass
from cocotbext.ofm.mvb.transaction import MvbTransaction, Transaction


@dataclass
class PprInstr(MvbTransaction):
    id : int = 0
    address : int = 0
    length : int = 0


@dataclass
class IdMemTr(Transaction):
    id : int = 0
    addr : int = 0
    words : int = 0
    eof_pos : int = 0
    tag_cnt : int = 0


@dataclass
class TagMemTr(Transaction):
    tag : int = 0
    addr : int = 0
    id : int = 0
