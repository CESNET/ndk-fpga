# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <ondrejschwarz@cesnet.cz>

from cocotb.types import Logic, LogicArray
from cocotbext.ofm.axi4stream.protocol import Axi4StreamProtocol
from cocotbext.ofm.base.protocol import optional_signal, alias


class Axi4sFrfrProtocol(Axi4StreamProtocol):
    AXI_TDATA       : LogicArray = alias(Axi4StreamProtocol.TDATA)
    AXI_TVALID      : Logic      = alias(Axi4StreamProtocol.TVALID)
    AXI_TREADY      : Logic      = alias(Axi4StreamProtocol.TREADY)
    AXI_TLAST       : Logic      = alias(Axi4StreamProtocol.TLAST)
    AXI_TKEEP       : LogicArray = alias(Axi4StreamProtocol.TKEEP)
    AXI_TUSER       : LogicArray = alias(Axi4StreamProtocol.TUSER)
    FRACTURE_EN     : Logic      = optional_signal()
    FRACTURE_OFFSET : LogicArray = optional_signal()
