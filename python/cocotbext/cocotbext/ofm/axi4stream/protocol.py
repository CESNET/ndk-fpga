# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <ondrej.schwarz@cesnet.cz>

from cocotbext.ofm.base.protocol import BusProtocol, parameter, signal, optional_signal
from cocotb.types import Logic, LogicArray


class Axi4StreamProtocol(BusProtocol):
    @parameter
    def TDATA_WIDTH(self) -> int:
        return len(self.TDATA) // 8

    @parameter
    def TKEEP_WIDTH(self) -> int:
        return len(self.TKEEP)

    @parameter
    def TDEST_WIDTH(self) -> int:
        try:
            return len(self.TDEST)
        except Exception:
            return 0

    @parameter
    def TID_WIDTH(self) -> int:
        try:
            return len(self.TID)
        except Exception:
            return 0

    @parameter
    def TUSER_WIDTH(self) -> int:
        try:
            return len(self.TUSER)
        except Exception:
            return 0

    @signal
    def TDATA(self, sigval) -> LogicArray:
        return sigval

    @TDATA.write()
    def TDATA(self, signal, value: bytes | LogicArray) -> None:
        if isinstance(value, bytes):
            value = LogicArray.from_bytes(value.ljust(self.TDATA_WIDTH, b"\x00"), self.TDATA_WIDTH * 8, byteorder="little")
        signal.value = value

    TVALID : Logic      = signal()
    TREADY : Logic      = signal()
    TLAST  : Logic      = optional_signal()
    TKEEP  : LogicArray = optional_signal()
    TSTRB  : LogicArray = optional_signal(put_with="TVALID")
    TDEST  : LogicArray = optional_signal(put_with="TVALID")
    TID    : LogicArray = optional_signal(put_with="TVALID")

    @optional_signal
    def TUSER(self, sigval) -> LogicArray:
        return sigval

    @TUSER.write()
    def TUSER(self, signal, value: bytes | int | LogicArray) -> None:
        if isinstance(value, bytes):
            value = int.from_bytes(value, "little")
        signal.value = value
