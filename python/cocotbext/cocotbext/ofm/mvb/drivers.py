# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <ondrejschwarz@cesnet.cz>
#            Daniel Kondys <kondys@cesnet.cz>


from cocotb.handle import ModifiableObject

from cocotbext.ofm.base.drivers import BusDriver

from typing import Any

from ..base.transaction import IdleTransaction
from .transaction import MvbTrClassic


class MVBDriver(BusDriver):
    """Driver intended for the MVB bus used for sending transactions to the bus.

    Atributes:
       _item_cnt(int): number of ready items in the current word.
       _data(dict): dictionary where "keys" are the names of the (optional) signals on the bus
                    and "values" are their respective current values.
    """

    _signals = ["vld", "src_rdy", "dst_rdy"]
    _optional_signals = ["data", "meta", "addr", "discard", "length", "key"]

    def __init__(self, entity, name, clock, array_idx=None) -> None:
        super().__init__(entity, name, clock, array_idx=array_idx)

        self.__os = [s for s in MVBDriver._optional_signals if hasattr(self.bus, s)]
        self.__item_cnt = 0
        self.__items = len(self.bus.vld)
        self.__bus_isarray = not isinstance(getattr(self.bus, self.__os[0]), ModifiableObject)
        self.__item_widths = self._get_item_widths()
        self.__data = self._init_data()

        self._clear_control_signals()
        self.bus.vld.value = 0
        self.bus.src_rdy.value = 0

    @property
    def os(self) -> list:
        """A list of names of optional signals that are on the bus
        (filtered version of the _optional_signals).
        """
        return self.__os

    @property
    def items(self) -> int:
        """The number of MVB items in word."""
        return self.__items

    @property
    def item_widths(self) -> dict:
        """A dictionary where "keys" are the names of the optional signals on the bus
        (items of the "os" list) and "values" are their respective widths.
        """
        return self.__item_widths

    @property
    def bus_isarray(self) -> bool:
        """Indicates whether the bus is a vector or an array."""
        return self.__bus_isarray

    def _get_item_widths(self) -> dict:
        """Make a dictionary of all optional signals on the bus and the width of each one's item."""

        if self.__bus_isarray:
            return {s: len(getattr(self.bus, s)[0]) for s in self.__os}
        else:
            return {s: len(getattr(self.bus, s)) // self.__items for s in self.__os}

    def _init_data(self) -> dict:
        """Make a dictionary of all optional signals on the bus and initialize their values."""

        if self.__bus_isarray:
            return {s: [0] * self.__items for s in self.__os}
        else:
            return {s: 0 for s in self.__os}

    def _clear_item(self) -> dict:
        """Return a clear Item (all data signals are 0)."""
        return {s: 0 for s in self.__os}

    def _clear_control_signals(self) -> None:
        """Sets control signals to default values without sending them to the MVB bus."""

        if self.__bus_isarray:
            for sig in self.__data:
                self.__data[sig] = [0] * self.__items
        else:
            for sig in self.__data:
                self.__data[sig] = 0
        self._vld = 0
        self._src_rdy = 0

    def _propagate_control_signals(self) -> None:
        """Sends value of control signals to the MVB bus."""

        for sig, val in self.__data.items():
            sig_obj = getattr(self.bus, sig)

            if isinstance(sig_obj, ModifiableObject):
                sig_obj.value = val
            else:
                for i in range(len(sig_obj)):
                    sig_obj[i].value = val[i]

        self.bus.vld.value = self._vld
        self.bus.src_rdy.value = self._src_rdy

    async def _stack_items(self, **kwargs) -> None:
        """Concatenates transactions (MVB Items) to form a word on the bus"""

        if self.__bus_isarray:
            for signal in self.__data:
                item_ptr = self.__item_cnt
                self.__data[signal][item_ptr] = kwargs.get(signal)
        else:
            for signal, value in self.__data.items():
                shift_size = self.__item_widths[signal] * self.__item_cnt
                tr_part = kwargs.get(signal)
                # Prepend the Item to the word: shift and OR
                self.__data[signal] = (tr_part << shift_size) | value

    async def _move_word(self) -> None:
        """Sends MVB word to the MVB bus if possible and clears the word."""

        self._src_rdy = 1 if self._vld > 0 else 0
        self._propagate_control_signals()

        await self._clk_re
        while self.bus.dst_rdy.value != 1:
            for _ in range(self.__items):
                self._idle_gen.put(self._idle_tr)
            await self._clk_re

        self._clear_control_signals()

    async def _driver_send(self, transaction: Any, sync: bool = True, **kwargs: Any) -> None:
        """Prepares and sends transaction to the MVB bus."""

        self.log.debug(f"Received item: {transaction}")

        if isinstance(transaction, IdleTransaction):
            mvb_tr = self._clear_item()
            item_vld = 0
        else:
            if isinstance(transaction, bytes):
                mvb_tr = MvbTrClassic.from_bytes(transaction)
            else:
                mvb_tr = transaction
            mvb_tr = {s: getattr(mvb_tr, s) for s in self.__os}
            item_vld = 1

        await self._stack_items(**mvb_tr)
        self._idle_gen.put(transaction)

        self._vld |= item_vld << self.__item_cnt
        self.__item_cnt += 1

        # self.log.debug("Current word state:")
        # self.log.debug(f"\t{self.__item_cnt}/{self.__items} Items filled")
        # self.log.debug(f"\tData: {self.__data}")

        if self.__item_cnt == self.__items:
            await self._move_word()
            self.__item_cnt = 0

    async def _send_thread(self) -> None:
        """Function used with cocotb testbench."""

        while True:
            while not self._sendQ:
                self._pending.clear()
                await self._pending.wait()

            while self._sendQ:
                transaction, callback, event, kwargs = self._sendQ.popleft()
                for _ in range(self._idle_gen.get(transaction)):
                    await self._send(self._idle_tr, callback=None, event=event, sync=False, **kwargs)
                await self._send(transaction, callback=None, event=event, sync=False, **kwargs)
                if event:
                    event.set()
                if callback:
                    callback(transaction)

            await self._move_word()
            await self._move_word()
