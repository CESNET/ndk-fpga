# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from cocotbext.ofm.base.protocol import optional_signal, alias
from cocotbext.ofm.base.types import LogicArray
from cocotbext.ofm.mvb.protocol import MvbProtocol


class PprDriverProtocol(MvbProtocol):
    regions : int        = alias(MvbProtocol.items)
    id      : LogicArray = optional_signal(put_with="vld")
    address : LogicArray = optional_signal(put_with="vld")
    length  : LogicArray = optional_signal(put_with="vld")


class PcieMvbProtocol(MvbProtocol):
    pcie_down_regions: int = alias(MvbProtocol.items)
    dma_downhdr_width: int = alias(MvbProtocol.item_width)
