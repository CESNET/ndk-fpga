# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

# TODO: read and return the value of the response signal for read and write in master

from typing import Optional

import cocotb
from cocotb.types import LogicArray
from cocotb.queue import Queue
from cocotb.triggers import Event, ClockCycles
from cocotbext.ofm.base.drivers import BusDriver
from cocotbext.ofm.utils.signals import await_signal_sync
from cocotbext.ofm.utils.math import ceildiv
from cocotbext.ofm.avmm.config import AvalonMMDataUnits, AvalonMMParams
from cocotbext.ofm.avmm.transaction import AvalonMMWriteRequestTransaction, AvalonMMReadRequestTransaction, AvalonMMReadResponseTransaction, AvalonMMWriteResponseTransaction, AvalonMMResponseValue
from cocotbext.ofm.utils.ram import RAM


class AvalonMMDriverMaster(BusDriver):
    _signals = []
    _optional_signals = ["address", "read", "readdata", "readdatavalid", "write", "writedata", "burstcount", "ready", "waitrequest"]

    def __init__(self, entity, name, clock, array_idx=None, params: Optional[AvalonMMParams] = None, **kwargs):
        super().__init__(entity, name, clock, array_idx, **kwargs)

        self._address_width    : int   = len(self.bus.address) if hasattr(self.bus, "address") else 0
        self._burstcount_width : int   = len(self.bus.burstcount) if hasattr(self.bus, "burstcount") else 0
        self._writedata_width  : int   = len(self.bus.writedata) if hasattr(self.bus, "writedata") else 0
        self._readdata_width   : int   = len(self.bus.readdata) if hasattr(self.bus, "readdata") else 0

        self._write_data_bytes : int   = self._writedata_width // 8
        self._read_data_bytes  : int   = self._readdata_width // 8

        self._response_queue   : Queue = Queue()
        self._request_queue    : Queue = Queue()

        # use default setting of parameters if they are not set by the user
        self._params = params if params is not None else AvalonMMParams()

        self._clear_control_signals()

        # start the request/response loops
        cocotb.start_soon(self._request_loop())
        cocotb.start_soon(self._response_loop())

    async def write(self, address: int, data: bytes, burst_count: Optional[int] = None, sync: bool = True):
        # create write transaction
        transaction = AvalonMMWriteRequestTransaction()
        transaction.address = address
        transaction.data = data
        transaction.burst_count = burst_count

        await self._send_write_request(transaction, sync)

    def send_write_request(self, transaction: AvalonMMWriteRequestTransaction, sync: bool = True) -> None:
        self._request_queue.put((transaction, sync))

    async def read(self, address: int, burst_count: Optional[int] = None, sync: bool = True) -> AvalonMMReadResponseTransaction:
        # create read request transactions
        transaction = AvalonMMReadRequestTransaction()
        transaction.address = address
        transaction.burst_count = burst_count
        transaction.event = Event()

        # send the transaction to the bus
        await self._send_read_request(transaction, sync)

        # wait for valid data
        await transaction.event.wait()
        # return the response
        return transaction.response

    def send_read_request(self, transaction: AvalonMMReadRequestTransaction, sync: bool = True):
        self._request_queue.put((transaction, sync))

    def _clear_control_signals(self):
        self._address     = LogicArray("X" * self._address_width)
        self._write_data  = LogicArray("X" * self._writedata_width)
        self._burst_count = LogicArray("X" * self._burstcount_width)
        self._read        = 0
        self._write       = 0
        self._ready       = 0

    def _propagate_control_signals(self):
        if hasattr(self.bus, "address"):
            self.bus.address.value = self._address
        if hasattr(self.bus, "read"):
            self.bus.read.value = self._read
        if hasattr(self.bus, "write"):
            self.bus.write.value = self._write
        if hasattr(self.bus, "writedata"):
            self.bus.writedata.value = self._write_data
        if hasattr(self.bus, "burstcount"):
            self.bus.burstcount.value = self._burst_count
        if hasattr(self.bus, "ready"):
            self.bus.ready.value = self._ready

    async def _write_word(self, address: int | LogicArray, word: int, sync: bool = True):
        if sync:
            await self._clk_re

        self._write      = 1
        self._address    = address
        self._write_data = word

        self._propagate_control_signals()

        await self._clk_re

        if hasattr(self.bus, "ready"):
            await await_signal_sync(self._clk_re, self.bus.ready)
        elif hasattr(self.bus, "waitrequest"):
            await await_signal_sync(self._clk_re, self.bus.waitrequest, 0)

        self._clear_control_signals()

    async def _write_burst(self, start_address: int, data: bytes, max_bursts: int, sync: bool = True) -> int:
        address  = start_address
        word_cnt = ceildiv(self._write_data_bytes, data)
        bursts   = word_cnt if word_cnt < max_bursts else max_bursts

        self._burst_count = bursts

        for _ in range(bursts):
            word = data[:self._write_data_bytes]
            data = data[self._write_data_bytes:]

            await self._write_word(address, int.from_bytes(word, "little"), sync)

            # clear the address since it's not needed anymore
            if address == start_address:
                address = LogicArray("X" * self._address_width)

        return bursts

    async def _send_write_request(self, transaction: AvalonMMWriteRequestTransaction, sync: bool = True) -> None:
        assert self._write_data_bytes > 0, "Write interface not present on the bus or is of null width."

        address     : int   = transaction.address
        data        : bytes = transaction.data
        burst_count : int   = transaction.burst_count
        slice_width : int   = burst_count * self._write_data_bytes if burst_count is not None else self._write_data_bytes

        while data:
            # get slice of the transaction
            data_slice = data[:slice_width]
            data = data[slice_width:]

            # write the word to the bus
            if burst_count is not None:
                actual_bursts = await self._write_burst(address, data_slice, max_bursts=burst_count, sync=sync)
                # increment the address corespondingly to the address units and lenght of the burst
                address += actual_bursts if self._params.addressUnits == AvalonMMDataUnits.words else len(data_slice)
            else:
                await self._write_word(address, int.from_bytes(data_slice, "little"), sync)
                # increment the address corespondingly to the address units
                address += 1 if self._params.addressUnits == AvalonMMDataUnits.words else len(data_slice)

    async def _send_read_request(self, transaction: AvalonMMReadRequestTransaction, sync: bool = True):
        if sync:
            await self._clk_re

        self._read    = 1
        self._address = transaction.address

        if transaction.burst_count is not None:
            self._burst_count = transaction.burst_count

        self._propagate_control_signals()

        await self._clk_re

        if hasattr(self.bus, "ready"):
            await await_signal_sync(self._clk_re, self.bus.ready)
        elif hasattr(self.bus, "waitrequest"):
            await await_signal_sync(self._clk_re, self.bus.waitrequest, 0)

        self._clear_control_signals()

        # put the transaction into the request queue
        await self._response_queue.put(transaction)

    async def _wait_for_read_response(self):
        # data is validated by the readdatavalid signal
        if hasattr(self.bus, "readdatavalid"):
            await await_signal_sync(self._clk_re, self.bus.readdatavalid)
        # fixed read latency
        elif self._params.readLatency > 0:
            for _ in range(self._params.readLatency):
                await self._clk_re
        # data is validated by the waitrequest signal rising to 1 and falling to 0
        elif hasattr(self.bus, "waitrequest"):
            await await_signal_sync(self._clk_re, self.bus.waitrequest, 1)
            await await_signal_sync(self._clk_re, self.bus.waitrequest, 0)
        # data is validated by the ready signal falling to 0 and rising to 1
        elif hasattr(self.bus, "ready"):
            await await_signal_sync(self._clk_re, self.bus.ready, 0)
            await await_signal_sync(self._clk_re, self.bus.ready, 1)

    async def _read_data_from_bus(self, burst_count: Optional[int] = None) -> bytes:
        data = b""

        if burst_count is not None:
            for _ in range(burst_count):
                await await_signal_sync(self._clk_re, self.bus.readdatavalid)
                data += self.bus.readdata.value.to_bytes(byteorder="little")
                await self._clk_re
        else:
            data = self.bus.readdata.value.to_bytes(byteorder="little")

        return data

    async def _request_loop(self):
        while True:
            while self._request_queue.empty():
                await self._clk_re

            # get request to be sent
            while not self._request_queue.empty():
                transaction, sync = await self._request_queue.get()

                if isinstance(transaction, AvalonMMWriteRequestTransaction):
                    await self._send_write_request(transaction, sync)
                else:
                    await self._send_read_request(transaction, sync)

    async def _response_loop(self):
        while True:
            while self._response_queue.empty():
                await self._clk_re

            while not self._response_queue.empty():
                # get request awaiting response
                request = await self._response_queue.get()
                # wait until valid read
                await self._wait_for_read_response()

                # read data from bus
                request.response.data = await self._read_data_from_bus(request.burst_count)
                request.event.set()

                await self._clk_re


class AvalonMMDriverSlave(BusDriver):
    _signals = []
    _optional_signals = ["address", "read", "readdata", "readdatavalid", "write", "writedata", "burstcount", "ready", "waitrequest"]

    def __init__(self, entity, name, clock, array_idx=None, params: Optional[AvalonMMParams] = None, ram: Optional[RAM] = None, **kwargs):
        super().__init__(entity, name, clock, array_idx, **kwargs)

        self._address_width    : int = len(self.bus.address) if hasattr(self.bus, "address") else 0
        self._burstcount_width : int = len(self.bus.burstcount) if hasattr(self.bus, "burstcount") else 0
        self._writedata_width  : int = len(self.bus.writedata) if hasattr(self.bus, "writedata") else 0
        self._readdata_width   : int = len(self.bus.readdata) if hasattr(self.bus, "readdata") else 0

        self._write_data_bytes : int = self._writedata_width // 8
        self._read_data_bytes  : int = self._readdata_width // 8

        # use default setting of parameters if they are not set by the user
        self._params = params if params is not None else AvalonMMParams()

        # backing memory, can be shared with other agents (e.g. a monitor or a second slave)
        address_space = 2 ** self._address_width - 1
        capacity  = address_space * self._write_data_bytes if self._params.addressUnits == AvalonMMDataUnits.words else address_space
        self._ram = ram if ram is not None else RAM(capacity)

        # pending transaction tracking
        self._pending_reads  : int  = 0
        self._pending_writes : int  = 0
        self._stall          : bool = False

        # queues for accepted requests waiting to be served
        self._response_queue : Queue = Queue()

        # start the acquisition and serving loops
        cocotb.start_soon(self._request_capture_loop())
        cocotb.start_soon(self._response_loop())

    def _clear_flow_control_signals(self):
        if hasattr(self.bus, "waitrequest"):
            self.bus.waitrequest.value = 1
        if hasattr(self.bus, "ready"):
            self.bus.ready.value = 0

    def _clear_response_control_signals(self):
        if hasattr(self.bus, "response"):
            self.bus.response.value = LogicArray("XX")
        if hasattr(self.bus, "readdata"):
            self.bus.readdata.value = LogicArray("X" * self._readdata_width)
        if hasattr(self.bus, "readdatavalid"):
            self.bus.readdatavalid.value = 0

    def _address_to_byte(self, address: int) -> int:
        # convert the bus address to a byte offset into the backing memory
        return address if self._params.addressUnits == AvalonMMDataUnits.symbols else address * self._write_data_bytes

    async def _async_read(self, transaction: AvalonMMReadRequestTransaction):
        if self._params.readLatency > 0:
            await ClockCycles(self.clock, self._params.readLatency)
        elif self._params.readWaitTime > 0:
            await ClockCycles(self.clock, self._params.readWaitTime)

        if transaction.burst_count > 0:
            addr = transaction.address

            for _ in range(transaction.burst_count):
                data = self._ram.r(self._address_to_byte(addr), self._read_data_bytes)
                addr += 1 if self._params.addressUnits == AvalonMMDataUnits.words else self._read_data_bytes

                response = AvalonMMReadResponseTransaction()
                response.response = AvalonMMResponseValue.OKAY
                response.data = data

                await self._response_queue.put(response)

        else:
            data = self._ram.r(self._address_to_byte(transaction.address), self._read_data_bytes)
            transaction.response.response = AvalonMMResponseValue.OKAY
            transaction.response.data = data
            await self._response_queue.put(transaction.response)

        self._pending_reads -= 1

    async def _async_write(self, transaction: AvalonMMWriteRequestTransaction):
        await ClockCycles(self.clock, self._params.writeWaitTime)
        self._ram.w(self._address_to_byte(transaction.address), transaction.data)

        transaction.response.response = AvalonMMResponseValue.OKAY
        await self._response_queue.put(transaction.response)
        self._pending_writes -= 1

    def _schedule_read(self, transaction: AvalonMMReadRequestTransaction):
        cocotb.start_soon(self._async_read(transaction))

    def _schedule_write(self, transaction: AvalonMMWriteRequestTransaction):
        cocotb.start_soon(self._async_write(transaction))

    def _update_flow_control(self):
        # stall the bus when either pending limit is reached
        read_full  = self._pending_reads >= self._params.maximumPendingReadTransactions
        write_full = self._params.maximumPendingWriteTransactions > 0 and self._pending_writes >= self._params.maximumPendingWriteTransactions

        self._stall = read_full or write_full

        if hasattr(self.bus, "ready"):
            self.bus.ready.value = 0 if self._stall else 1
        if hasattr(self.bus, "waitrequest"):
            self.bus.waitrequest.value = 1 if self._stall else 0

    async def _request_capture_loop(self):
        self._clear_flow_control_signals()

        while True:
            await self._clk_re
            self._update_flow_control()

            # if no more requests can be accepted, wait
            if self._stall:
                continue

            write = self.bus.write.value if hasattr(self.bus, "write") else 0
            read  = self.bus.read.value if hasattr(self.bus, "read") else 0

            assert not write or not read, "Read and write signals were set at the same time."

            # capture a the request
            if read or write:
                address = self.bus.address.value.to_unsigned()

                # try to get value of burst count - can fail if it's not on the bus or not set
                try:
                    burst_count = self.bus.burstcount.value.to_unsigned()
                except Exception:
                    burst_count = 0

                if read:
                    transaction = AvalonMMReadRequestTransaction()
                    transaction.address = address
                    transaction.burst_count = burst_count
                    transaction.event = Event()

                    self._schedule_read(transaction)
                    self._pending_reads += 1

                if write:
                    transaction = AvalonMMWriteRequestTransaction()
                    transaction.address = address
                    transaction.burst_count = burst_count
                    transaction.data = b""

                    if burst_count > 0:
                        for i in range(burst_count):
                            await await_signal_sync(self._clk_re, self.bus.write)
                            transaction.data += self.bus.writedata.value.to_bytes(byteorder="little")

                            if i < burst_count - 1:
                                await self._clk_re
                    else:
                        transaction.data = self.bus.writedata.value.to_bytes(byteorder="little")

                    self._schedule_write(transaction)
                    self._pending_writes += 1

    async def _response_loop(self):
        self._clear_response_control_signals()

        while True:
            while self._response_queue.empty():
                await self._clk_re

            while not self._response_queue.empty():
                response = await self._response_queue.get()

                if hasattr(self.bus, "response"):
                    self.bus.response.value = response.response.value
                else:
                    # if response signal is not present of bus, write transaction should not cause response delay
                    if isinstance(response, AvalonMMWriteResponseTransaction):
                        continue

                if hasattr(response, "data") and hasattr(self.bus, "readdata"):
                    self.bus.readdata.value = int.from_bytes(response.data, "little")

                    if hasattr(self.bus, "readdatavalid"):
                        self.bus.readdatavalid.value = 1

                await self._clk_re

                self._clear_response_control_signals()
