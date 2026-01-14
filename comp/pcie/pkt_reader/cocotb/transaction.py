# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>

from dataclasses import dataclass
from cocotbext.ofm.mvb.transaction import MvbTransaction
from cocotbext.ofm.mfb.transaction import MfbTransaction


@dataclass
class PprInstr(MvbTransaction):
    id : int = 0
    address : int = 0
    length : int = 0


@dataclass(slots=True)
class PprData(MfbTransaction):
    id : int = 0
