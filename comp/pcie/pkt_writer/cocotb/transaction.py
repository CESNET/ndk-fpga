# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>

from dataclasses import dataclass
from cocotbext.ofm.mvb.transaction import MvbTransaction


@dataclass
class MvbTrAddressAndLength(MvbTransaction):
    address : int = 0
    length : int = 0
