# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from cocotb.types import LogicArray
from cocotbext.ofm.base.protocol import alias, optional_signal
from cocotbext.ofm.mvb.protocol import MvbProtocol


class MvbProtocolWithAddressAndLength(MvbProtocol):
    mfb_regions : int        = alias(MvbProtocol.items)
    address     : LogicArray = optional_signal(put_with="vld")
    length      : LogicArray = optional_signal(put_with="vld")
