# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from cocotb.types import Logic
from cocotbext.ofm.base.types import LogicArray
from cocotbext.ofm.base.protocol import BusProtocol, parameter, generic, signal, optional_signal, alias


class MvbProtocol(BusProtocol):
    items      : int = generic()
    item_width : int = generic()

    @parameter
    def word_width(self):
        return self.items * self.item_width

    src_rdy : Logic      = signal()
    dst_rdy : Logic      = signal()
    vld     : LogicArray = optional_signal()
    data    : LogicArray = optional_signal()
    meta    : LogicArray = optional_signal()


class MvbProtocolWithRegions(MvbProtocol):
    regions: int = alias(MvbProtocol.items)
