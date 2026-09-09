# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from cocotb.types import LogicArray
from cocotbext.ofm.base.protocol import optional_signal
from cocotbext.ofm.mvb.protocol import MvbProtocol


class PprDriverProtocol(MvbProtocol):
    id      : LogicArray = optional_signal(put_with="vld")
    address : LogicArray = optional_signal(put_with="vld")
    length  : LogicArray = optional_signal(put_with="vld")
