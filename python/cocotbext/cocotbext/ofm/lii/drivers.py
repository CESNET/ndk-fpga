# drivers.py: LIIDriver
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import random
from cocotb_bus.drivers import BusDriver
from cocotb.triggers import RisingEdge


class LIIDriver(BusDriver):
    _signals = ["d", "db", "sof", "eof", "rdy", "crcok", "crcvld"]

    def __init__(self, entity, name, clock, array_idx=None):
        BusDriver.__init__(self, entity, name, clock, array_idx=array_idx)
        self.clock = clock
        self._bytes = len(self.bus.d) // 8
        self._block_size = 4 if self._bytes <= 4 else 8
        self._clear_signals()
        self._data = bytearray(self._bytes)
        self._valid_bytes = 0
        self._sof_flag = 0
        self._eof_flag = 0
        self._vld_flag = 0
        self._offset = 0 # in bytes
        self._blk_idx = self._offset // self._block_size
        self._blk_pos = self._offset % self._block_size
        self.frame_cnt = 0

    def _clear_signals(self):
        self._sof_flag = 0
        self._eof_flag = 0
        self._vld_flag = 0
        self._valid_bytes = 0

        self.bus.sof.value = random.randint(0, 1)
        self.bus.eof.value = random.randint(0, 1)
        self.bus.db.value = random.randint(0, 4)
        self.bus.rdy.value = 0
        self.bus.crcok.value = random.randint(0, 1)
        self.bus.crcvld.value = 0

    async def _move_byte(self):
        self._offset += 1
        if (self._offset >= self._bytes):
            await self._write_word()

        self._blk_idx = self._offset // self._block_size
        self._blk_pos = self._offset % self._block_size

    async def _write_word(self):
        self.bus.d.value = int.from_bytes(self._data, 'little')
        self.bus.sof.value = self._sof_flag
        self.bus.eof.value = self._eof_flag
        self.bus.db.value = self._valid_bytes
        self.bus.rdy.value = self._vld_flag

        #print("==== WORD ====")
        #print("data        : " + self._data.hex())
        #print("sof_flag    : " + str(self._sof_flag))
        #print("eof_flag    : " + str(self._eof_flag))
        #print("valid_bytes : " + str(self._valid_bytes))
        #print("vld_flag    : " + str(self._vld_flag))
        #print("crc_flag    : " + str(self.bus.crcvld.value))

        # Random (1 to 5) idle cycles
        for ii in range(random.randint(1, 6)):
            await RisingEdge(self.clock)
            self._clear_signals()
            self._offset = 0

    async def _send_transaction(self, transaction):
        while (self._blk_pos != 0) or (self._sof_flag != 0) or (self._vld_flag != 0):
            await self._move_byte()

        for bb in range(0, len(transaction)):
            self._vld_flag = 1
            self._valid_bytes += 1
            self._data[self._offset] = transaction[bb]

            if bb == 0:
                # set SOF flag
                self._sof_flag = 2**self._blk_idx

            # EOF flag
            if bb == (len(transaction) - 1):
                # Move EOF flag to next word
                if (random.randint(0, 8) > 2) and (self._offset == (self._bytes - 1)):
                    await self._write_word()
                    self._vld_flag = 1
                    self._eof_flag = 1
                    self._valid_bytes = 0
                else:
                    # EOF flag with non-zero bytes
                    self._eof_flag = 1

            await self._move_byte()

        await self._send_crc_status(1)

    async def _send_crc_status(self, crc_status):
        # Random idle bytes
        for ii in range(random.randint(4, 4 * self._bytes)):
            await self._move_byte()

        while (self.bus.crcvld.value == 1) or (self._vld_flag != 0):
            await self._move_byte()

        self.bus.crcok.value = crc_status
        self.bus.crcvld.value = 1

    async def _send_thread(self):
        while True:
            # Sleep until we have something to send
            while not self._sendQ:
                self._pending.clear()
                await self._pending.wait()

            await self._write_word()

            while self._sendQ:
                transaction, callback, event, kwargs = self._sendQ.popleft()

                await self._send_transaction(transaction)
                self.frame_cnt += 1

                if event:
                    event.set()

                if callback:
                    callback(transaction)

            await self._write_word()
            await self._write_word()
