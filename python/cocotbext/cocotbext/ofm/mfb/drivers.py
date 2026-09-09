# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2024-2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from cocotbext.ofm.base.drivers import ModularBusDriver
from cocotbext.ofm.base.transaction import IdleTransaction
from cocotbext.ofm.mfb.transaction import MfbTransaction
from cocotb.types import Logic, LogicArray
from cocotbext.ofm.base.types import LogicArray2D
from cocotbext.ofm.utils.math import ceildiv
from cocotbext.ofm.mfb.protocol import MfbProtocol

from dataclasses import dataclass, asdict


class MFBDriver(ModularBusDriver):
    bus: MfbProtocol

    @dataclass
    class State:
        DATA    : LogicArray | bytearray = 0
        SOF_POS : LogicArray2D           = 0
        EOF_POS : LogicArray2D           = 0
        SOF     : LogicArray             = 0
        EOF     : LogicArray             = 0
        SRC_RDY : Logic                  = 0
        META    : LogicArray2D           = 0

    def __init__(self, dut, name, clock, protocol=MfbProtocol, no_inner_idles: bool = False, **kwargs):
        super().__init__(dut, name, clock, protocol=protocol, **kwargs)

        self._item_width     : int = self.bus.ITEM_WIDTH
        self._word_bytes     : int = self.bus.WORD_WIDTH // 8
        self._item_bytes     : int = self.bus.ITEM_WIDTH // 8
        self._block_bytes    : int = self.bus.BLOCK_SIZE * self._item_bytes
        self._region_bytes   : int = self._block_bytes * self.bus.REGION_SIZE
        self._regions        : int = self.bus.REGIONS
        self._region_items   : int = self.bus.REGION_SIZE * self.bus.BLOCK_SIZE

        self._no_inner_idles : bool = no_inner_idles

        self._staged_items   : int = 0
        self._item_cnt       : int = 0
        self._frame_cnt      : int = 0

    @property
    def item_cnt(self):
        return self._item_cnt

    @property
    def frame_cnt(self):
        return self._frame_cnt

    def _init_state(self):
        self.state: MFBDriver.State = MFBDriver.State()

    def _clear_signals(self):
        self._auto_clear_signals()
        self.state.DATA    = bytearray(self.bus.WORD_WIDTH // 8)
        self.state.SOF_POS = LogicArray2D.from_logicarray(self.state.SOF_POS, self.bus.REGIONS)
        self.state.EOF_POS = LogicArray2D.from_logicarray(self.state.EOF_POS, self.bus.REGIONS)
        self.state.SOF     = LogicArray(0, self.bus.REGIONS)
        self.state.EOF     = LogicArray(0, self.bus.REGIONS)
        self.state.SRC_RDY = 0

        # converting signals valid with SOF or EOF to LogicArray2D
        for name in self.bus.optional_signals.keys():
            put_with = self.bus.put_with(name)

            if put_with == "SOF" or put_with == "EOF":
                value = getattr(self.state, name)
                setattr(self.state, name, LogicArray2D.from_logicarray(value, self.bus.REGIONS))

    async def _split_transaction(self, transaction: MfbTransaction | IdleTransaction):
        word_is_full  : bool = False
        word_overflow : bool = False
        region_offset : int  = 0
        byte_offset   : int  = 0

        while not word_is_full:
            if isinstance(transaction, MfbTransaction):
                while transaction.data:
                    # get a slice of data from the transaction to the end of the width of a word
                    data = transaction.data[:self._word_bytes - byte_offset]

                    # if a transaction has already started or ended in this region, put it in the next region
                    if self.state.SOF[region_offset] or self.state.EOF[region_offset]:
                        region_offset += 1

                        # if all regions are full, send the transaction
                        if region_offset >= self._regions:
                            region_offset = 0
                            yield

                        # set the byte offset to the start of the new region
                        byte_offset = region_offset * self._region_bytes
                        # get the data from the transaction again
                        continue

                    sof_pos   = None
                    sof_index = None

                    # set SOF if the packet has not started in the previous word
                    if not word_overflow:
                        self.state.SOF[region_offset] = 1
                        sof_pos = (byte_offset % self._region_bytes) // self._block_bytes
                        sof_index = region_offset
                        self.state.SOF_POS[region_offset] = LogicArray.from_unsigned(sof_pos, len(self.state.SOF_POS[region_offset]))
                    else:
                        word_overflow = False

                    # check for overflow
                    if len(data) != len(transaction.data):
                        word_overflow = True

                    # set DATA
                    self.state.DATA[byte_offset:byte_offset + len(data)] = data

                    # count the items
                    self._staged_items += (len(data) * 8) // self._item_width

                    # remove the part of the data being sent from the transaction
                    transaction.data = transaction.data[self._word_bytes - byte_offset:]

                    # increase the offset
                    byte_offset  += len(data)
                    region_offset = (byte_offset - 1) // self._region_bytes

                    eof_pos   = None
                    eof_index = None

                    # set EOF if the packet does not overflow to the next word
                    if not word_overflow:
                        self.state.EOF[region_offset] = 1
                        eof_pos = ((byte_offset - 1) % self._region_bytes) // self._item_bytes
                        eof_index = region_offset
                        self.state.EOF_POS[region_offset] = LogicArray.from_unsigned(eof_pos, len(self.state.EOF_POS[region_offset]))

                    # set optional signals automatically
                    self._auto_set_optional_signals(transaction, sof_index, eof_index)

                    # align the byte offset to the next block and region offset to the next region
                    byte_offset   = ceildiv(self._block_bytes, byte_offset) * self._block_bytes
                    region_offset = byte_offset // self._region_bytes

                    # check if the word if full
                    word_is_full = byte_offset >= self._word_bytes

                    # when the word is full, send it to the bus
                    if word_is_full:
                        byte_offset = 0
                        region_offset = 0
                        yield

            elif isinstance(transaction, IdleTransaction):
                if self._no_inner_idles:
                    yield
                    return

                remaining_idle_bytes = len(transaction)

                while remaining_idle_bytes:
                    free_bytes = self._word_bytes - byte_offset

                    if free_bytes <= remaining_idle_bytes:
                        self.state.DATA[byte_offset:] = free_bytes * b"\x00"
                        byte_offset += free_bytes
                        remaining_idle_bytes -= free_bytes
                    else:
                        self.state.DATA[byte_offset:byte_offset + remaining_idle_bytes] = remaining_idle_bytes * b"\x00"
                        byte_offset += remaining_idle_bytes
                        remaining_idle_bytes = 0

                    byte_offset   = ceildiv(self._block_bytes, byte_offset) * self._block_bytes
                    region_offset = byte_offset // self._region_bytes

                    word_is_full = byte_offset >= self._word_bytes

                    # when the word is full, send it to the bus
                    if byte_offset >= self._word_bytes:
                        byte_offset = 0
                        region_offset = 0
                        yield

            # if the word is not yet full, get the next transaction
            if not word_is_full:
                transaction = await anext(self._transactions)

    async def _send_to_bus(self):
        self.state.SRC_RDY = 1
        self._write_to_bus()

        await self._clk_re

        while not self.bus.DST_RDY:
            await self._clk_re

        self._frame_cnt += self.state.EOF.count("1")

    def _get_sent_items(self):
        items = self._staged_items
        self._staged_items = 0
        return items

    def _auto_set_optional_signals(self, transaction: MfbTransaction, sof_index: int, eof_index: int):
        """Automatically assings value to optional signals present in the transaction."""
        for name, value in asdict(transaction).items():
            name = name.upper()

            if name in self.bus.optional_signals:
                put_with = self.bus.put_with(name)

                if put_with is None:
                    continue

                if put_with == "SOF" or put_with == "EOF":
                    index = sof_index if put_with == "SOF" else eof_index

                    if index is None:
                        continue

                    if getattr(self.state, put_with)[index]:
                        sigval = getattr(self.state, name)
                        sigval[index] = value
                else:
                    if getattr(self.state, put_with):
                        setattr(self.state, name, value)
