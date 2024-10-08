# drivers.py: MVBDriver
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <Ondrej.Schwarz@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

from cocotbext.ofm.base.drivers import BusDriver
from cocotbext.ofm.mvb.utils import random_delays_config

import random


class MVBDriver(BusDriver):
    """Driver intender for the MVB bus used for sending transactions to the bus.

    Atributes:
       _item_cnt(int): number of items sent.
       _vld_item_cnt(int): number of valid items sent (without items containing random spaces).
       _items(int): number of MVB items.
       _word_width(int): width of MVB word in bytes.
       _item_width(int): width of MVB item in bytes.
       _item_offset(int): offset of MVB item in context of MVB word.

    """

    _signals = ["data", "vld", "src_rdy", "dst_rdy"]

    def __init__(self, entity, name, clock, array_idx=None, mvb_params={}) -> None:
        super().__init__(entity, name, clock, array_idx=array_idx)
        self._item_cnt = 0
        self._vld_item_cnt = 0
        self._items = len(self.bus.vld)
        self._word_width = len(self.bus.data) // 8
        self._item_width = self._word_width // self._items
        self._item_offset = 0
        self._clear_control_signals()
        self.bus.src_rdy.value = 0

        self._cDelays, self._mode, self._delays_fill = random_delays_config(self._items, mvb_params)
        """Randomized empty spaces"""

    def _clear_control_signals(self) -> None:
        """Sets control signals to default values without sending them to the MVB bus."""

        self._data = bytearray(self._word_width)
        self._vld = 0
        self._src_rdy = 0

    def _propagate_control_signals(self) -> None:
        """Sends value of control signals to the MVB bus."""

        self.bus.data.value = int.from_bytes(self._data, 'little')
        self.bus.vld.value = self._vld
        self.bus.src_rdy.value = self._src_rdy

    def _fill_empty_word(self) -> None:
        """Fills MVB word with invalid data."""

        for i in range(self._word_width):
            if self._mode == 1 or self._mode == 3:
                self._data[i] = self._delays_fill
            elif self._mode == 2:
                self._data[i] = random.randrange(0, 256)
        self._vld = 0

    async def _move_item(self) -> None:
        """Moves MVB item in context of MVB word and if the word is full, it is fowarded to the _move_word function."""

        self._item_offset += 1

        if self._item_offset == self._items:
            await self._move_word()
            self._item_offset = 0

    async def _move_word(self) -> None:
        """Sends MVB word to the MVB bus if possible and clears the word."""

        if (self._src_rdy):
            self._propagate_control_signals()

        else:
            self._clear_control_signals()
            self.bus.src_rdy.value = 0

        #TODO when Utils are merged, replace with await_signal_sync
        while True:
            await self._clk_re
            if self.bus.dst_rdy.value == 1:
                break

        if random.choices((0, 1), weights=self._cDelays["wordDelayEn_wt"], k=1)[0]:
            for i in self._cDelays["wordDelay"]:
                self._fill_empty_word()
                self._src_rdy = 1
                self._item_cnt += self._items
                self._propagate_control_signals()

        self._clear_control_signals()

    async def _send_data(self, data: bytes) -> None:
        """Prepares and sends transaction to the MVB bus.

           Args:
               data - data to be sent to the MVB bus.

        """

        self.log.debug(f"ITEM {self._vld_item_cnt}:")
        self.log.debug(f"sending item: {data}")

        self._data[self._item_offset * self._item_width:(self._item_offset + 1) * self._item_width] = data

        self.log.debug(f"word: {self._data}")

        self._vld += 1 << (self._item_cnt % self._items)

        self.log.debug(f"item vld: {1 << (self._item_cnt % self._items)}")
        self.log.debug(f"word vld: {self._vld}")

        self._src_rdy = 1

        self._item_cnt += 1
        self._vld_item_cnt += 1

        await self._move_item()

        if random.choices((0, 1), weights=self._cDelays["ivgEn_wt"], k=1)[0]:
            for i in self._cDelays["ivg"]:
                if self._mode:
                    for i in range(self._item_width):
                        if self._mode == 2:
                            self._delays_fill = random.randrange(0, 256)
                        self._data[self._item_offset * self._item_width + i] = self._delays_fill
                else:
                    self._data[self._item_offset * self._item_width:(self._item_offset + 1) * self._item_width] = data

                self._src_rdy = 1
                self._item_cnt += 1
                await self._move_item()

    async def _send_thread(self) -> None:
        """Function used with cocotb testbench."""

        while True:
            while not self._sendQ:
                self._pending.clear()
                await self._pending.wait()

            while self._sendQ:
                transaction, callback, event, kwargs = self._sendQ.popleft()
                assert len(transaction) == self._item_width
                await self._send_data(transaction)
                if event:
                    event.set()
                if callback:
                    callback(transaction)

            await self._move_word()
            await self._move_word()
