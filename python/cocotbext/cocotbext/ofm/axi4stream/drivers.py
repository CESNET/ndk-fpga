# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025-2026 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#            Ondrej Schwarz <ondrejschwarz@cesnet.cz>


from cocotbext.ofm.base.drivers import BusDriver, ModularBusDriver
from cocotbext.ofm.axi4stream.transaction import Axi4StreamTransaction
from cocotbext.ofm.axi4stream.protocol import Axi4StreamProtocol
from cocotbext.ofm.utils.math import bitmask
from cocotb.types import Logic, LogicArray
from cocotb.handle import Immediate
from dataclasses import dataclass


class Axi4StreamMaster(ModularBusDriver):
    bus: Axi4StreamProtocol

    @dataclass
    class State:
        TDATA  : LogicArray = 0
        TUSER  : LogicArray = 0
        TKEEP  : LogicArray = 0
        TSTRB  : LogicArray = 0
        TID    : LogicArray = 0
        TDEST  : LogicArray = 0
        TLAST  : Logic      = 0
        TVALID : Logic      = 0

    def __init__(self, *args, protocol=Axi4StreamProtocol, **kwargs):
        super().__init__(*args, protocol=protocol, **kwargs)

    def _init_state(self):
        self.state: Axi4StreamMaster.State = Axi4StreamMaster.State()

    def _clear_signals(self):
        self._auto_clear_signals()
        self.state.TVALID = 0
        self.state.TLAST  = 0

    async def _split_transaction(self, transaction: Axi4StreamTransaction):
        data_width = self.bus.TDATA_WIDTH
        user_width = self.bus.TUSER_WIDTH // 8

        while transaction.TDATA:
            self.state.TDATA  = transaction.TDATA[:data_width]
            self.state.TUSER  = transaction.TUSER[:user_width]
            self.state.TKEEP  = LogicArray.from_unsigned(bitmask(len(self.state.TDATA)), self.bus.TKEEP_WIDTH)
            self.state.TSTRB  = self.state.TKEEP
            self.state.TLAST  = 0
            self.state.TVALID = 1

            transaction.TDATA = transaction.TDATA[data_width:]
            transaction.TUSER = transaction.TUSER[user_width:]

            if len(transaction.TDATA) == 0:
                self.state.TLAST = 1

            self._auto_set_optional_signals(transaction)

            yield

    async def _send_to_bus(self):
        self._write_to_bus()

        await self._clk_re

        while not self.bus.TREADY:
            await self._clk_re


class Axi4StreamSlave(BusDriver):
    _signals = ["TVALID", "TREADY"]

    def __init__(self, entity, name, clock, array_idx=None):
        super().__init__(entity, name, clock, array_idx=array_idx)

        self.bus.TREADY.set(Immediate(1))
