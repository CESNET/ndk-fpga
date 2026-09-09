# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025-2026 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <ondrejschwarz@cesnet.cz>
#            Daniel Kondys <kondys@cesnet.cz>

from cocotb.types import Logic, LogicArray

from cocotbext.ofm.base.drivers import ModularBusDriver

from dataclasses import dataclass

from ..base.transaction import IdleTransaction
from ..base.types import LogicArray2D
from .transaction import MvbTransaction
from .protocol import MvbProtocol


class MVBDriver(ModularBusDriver):
    bus: MvbProtocol

    @dataclass
    class State:
        src_rdy : Logic        = 0
        data    : LogicArray2D = 0
        meta    : LogicArray2D = 0
        vld     : LogicArray   = 0

    def __init__(self, *args, protocol=MvbProtocol, **kwargs):
        super().__init__(*args, protocol=protocol, **kwargs)

    def _init_state(self):
        self.state: MVBDriver.State = MVBDriver.State()

    def _clear_signals(self):
        self.state.src_rdy = 0

        for name in self.bus.optional_signals.keys():
            value = getattr(self.bus, name)
            width = len(value)

            if isinstance(value, LogicArray2D):
                width *= len(value.item_range)
            elif isinstance(value, bytes):
                width *= 8

            width_per_item = width // self.bus.items
            ser_value = LogicArray("X" * width)
            value = LogicArray2D.from_logicarray(ser_value, self.bus.items) if width_per_item > 1 else ser_value

            setattr(self.state, name, value)

    async def _split_transaction(self, transaction: MvbTransaction):
        for i in range(self.bus.items):
            if not isinstance(transaction, IdleTransaction):
                self.state.vld[i] = 1

                for name in self.bus.optional_signals.keys():
                    if hasattr(transaction, name):
                        value = getattr(transaction, name)
                        put_with = self.bus.put_with(name)
                        is_valid = getattr(self.state, put_with) if put_with is not None else True

                        if is_valid:
                            signal = getattr(self.state, name)
                            signal[i] = value
            else:
                self.state.vld[i] = 0

            if i != self.bus.items - 1:
                transaction = await anext(self._transactions)

        self.state.src_rdy = 1
        yield

    def _write_to_bus(self):
        for name in self.bus.signals.keys():
            if hasattr(self.state, name):
                value = getattr(self.state, name)

                if isinstance(value, LogicArray2D):
                    value = value.serialize()

                setattr(self.bus, name, value)

    async def _send_to_bus(self):
        self._write_to_bus()

        await self._clk_re

        while not self.bus.dst_rdy:
            await self._clk_re
