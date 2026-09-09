# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from cocotb.types import Logic
from cocotbext.ofm.base.types import LogicArray, LogicArray2D
from cocotbext.ofm.base.protocol import BusProtocol, parameter, generic, signal, optional_signal
from math import log2
from dataclasses import dataclass


@dataclass
class MfbParams:
    regions     : int = 0
    region_size : int = 0
    block_size  : int = 0
    item_width  : int = 0


class MfbProtocol(BusProtocol):
    REGIONS     : int = generic()
    REGION_SIZE : int = generic()
    BLOCK_SIZE  : int = generic()
    ITEM_WIDTH  : int = generic()

    @parameter
    def WORD_WIDTH(self):
        return self.REGIONS * self.REGION_SIZE * self.BLOCK_SIZE * self.ITEM_WIDTH

    @parameter
    def SOF_POS_WIDTH(self):
        return self.REGIONS * log2(self.REGION_SIZE)

    @parameter
    def EOF_POS_WIDTH(self):
        return self.REGIONS * log2(self.REGION_SIZE * self.BLOCK_SIZE)

    @parameter
    def META_WIDTH(self):
        return self.dut.META_WIDTH

    @signal
    def DATA(self, sigval) -> LogicArray:
        return sigval

    @DATA.write()
    def DATA(self, signal, value: LogicArray | bytearray | bytes) -> None:
        if isinstance(value, bytearray) or isinstance(value, bytes):
            value = LogicArray.from_bytes(bytes(value).ljust(self.WORD_WIDTH // 8, b"\x00"), self.WORD_WIDTH, byteorder="little")
        signal.value = value

    @signal
    def SOF_POS(self, sigval) -> LogicArray:
        return sigval

    @SOF_POS.write()
    def SOF_POS(self, signal, value: LogicArray2D) -> None:
        signal.value = value.serialize()

    @signal
    def EOF_POS(self, sigval) -> LogicArray:
        return sigval

    @EOF_POS.write()
    def EOF_POS(self, signal, value: LogicArray2D) -> None:
        signal.value = value.serialize()

    SOF     : LogicArray = signal()
    EOF     : LogicArray = signal()
    SRC_RDY : Logic      = signal()
    DST_RDY : Logic      = signal()

    @optional_signal.read(put_with="SOF")
    def META(self, sigval: LogicArray) -> LogicArray:
        return sigval

    @META.write(put_with="SOF")
    def META(self, signal, value: LogicArray2D) -> None:
        signal.value = value.serialize()
