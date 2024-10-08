# drivers.py: MFBDriver
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

from cocotb_bus.drivers import BusDriver
from cocotb.triggers import RisingEdge
from cocotbext.ofm.mfb.utils import get_mfb_params

import copy


class MFBDriver(BusDriver):
    _signals = ["data", "sof_pos", "eof_pos", "sof", "eof", "src_rdy", "dst_rdy"]

    def __init__(self, entity, name, clock, array_idx=None, mfb_params=None):
        BusDriver.__init__(self, entity, name, clock, array_idx=array_idx)
        self.clock = clock
        self.frame_cnt = 0
        self._regions, self._region_size, self._block_size, self._item_width = get_mfb_params(
            self.bus.data, self.bus.sof_pos, self.bus.eof_pos, self.bus.sof, mfb_params
        )
        self._items = self._regions * self._region_size * self._block_size
        self._region_items = self._region_size * self._block_size
        self._item_offset = 0
        self._clear_control_signals()
        self.bus.src_rdy.value = 0

    def _clear_control_signals(self):
        self._data = bytearray(self._items)
        self._sof_pos = [0] * self._regions
        self._eof_pos = [0] * self._regions
        self._sof = [0] * self._regions
        self._eof = [0] * self._regions
        self._src_rdy = 0

    def _fillEmptyItems(self):
        for ii in range(self._block_size):
            self._data[self._item_offset + ii] = 0

    async def _moveBlock(self):
        self._item_offset = self._item_offset + self._block_size
        if (self._item_offset >= self._items):
            await self._moveWord()

    def _writeWord(self):
        sof_value = 0
        eof_value = 0
        sof_pos_value = 0
        eof_pos_value = 0

        for rr in range(self._regions):
            sof_value |= self._sof[rr] << rr
            eof_value |= self._eof[rr] << rr
            if (self._region_size > 1):
                sof_pos_value |= self._sof_pos[rr] << (rr * (len(self.bus.sof_pos) // self._regions))
            eof_pos_value |= self._eof_pos[rr] << (rr * (len(self.bus.eof_pos) // self._regions))

        self.bus.data.value = int.from_bytes(self._data, 'little')
        self.bus.sof.value = sof_value
        self.bus.eof.value = eof_value
        if (self._region_size > 1):
            self.bus.sof_pos.value = sof_pos_value
        self.bus.eof_pos.value = eof_pos_value
        self.bus.src_rdy.value = self._src_rdy

    def _fillEmptyWord(self):
        self._data = bytearray(self._items)
        self._sof_pos = [0] * self._regions
        self._eof_pos = [0] * self._regions
        self._sof = [0] * self._regions
        self._eof = [0] * self._regions
        self._src_rdy = 0

    async def _moveWord(self):
        re = RisingEdge(self.clock)
        if (self._src_rdy):
            self._writeWord()
        else:
            self._fillEmptyWord()
            self.bus.src_rdy.value = 0

        while True:
            await re
            if self.bus.dst_rdy.value == 1:
                break

        self._clear_control_signals()
        self._item_offset = 0

    async def _write_frame(self, data):
        data = copy.copy(data)
        data_len = len(data)

        while data:
            r = self._item_offset // self._region_items
            p = self._item_offset % self._region_items

            #print("self._item_offset " + str(self._item_offset))
            #print("self._region_items " + str(self._region_items))
            #print("r " + str(r))
            #print("p " + str(p))

            # two SOFs not allowed in the same region
            while self._sof[r]:
                self._fillEmptyItems()
                await self._moveBlock()

            ep = self._item_offset + data_len - 1 # end offset position
            er = ep // self._region_items # end region

            # two EOFs not allowed in the same region
            while ((er < self._regions) and self._eof[er]):
                self._fillEmptyItems()
                await self._moveBlock()

            # mark SOF
            r = self._item_offset // self._region_items
            p = self._item_offset % self._region_items
            self._sof[r] = 1
            self._sof_pos[r] = p // self._block_size

            while (len(data) > 0):
                if (len(data) > self._block_size):
                    # write data block
                    self._data[self._item_offset: (self._item_offset + self._block_size)] = data[:self._block_size]
                    data = data[self._block_size:]
                    #print("write data block")

                    self._src_rdy = 1
                    await self._moveBlock()
                else: # last data block
                    self._fillEmptyItems()

                    # mark EOF
                    r = self._item_offset // self._region_items
                    p = self._item_offset % self._region_items
                    self._eof[r] = 1
                    self._eof_pos[r] = p + len(data) - 1

                    # copy data block
                    self._data[self._item_offset: (self._item_offset + len(data))] = data[:self._block_size]
                    data = data[self._block_size:]
                    #print("write last data block")

                    self._src_rdy = 1
                    await self._moveBlock()

    async def _send_thread(self):
        while True:
            # Sleep until we have something to send
            while not self._sendQ:
                self._pending.clear()
                await self._pending.wait()

            while self._sendQ:
                transaction, callback, event, kwargs = self._sendQ.popleft()
                await self._write_frame(transaction)
                self.frame_cnt += 1
                # Notify the world that this transaction is complete
                if event:
                    event.set()
                if callback:
                    callback(transaction)

            await self._moveWord()
            await self._moveWord()
