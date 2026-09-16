# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

# TODO: read and return the value of the response signal for read and write in master

from typing import Optional

import cocotb
from cocotb.types import LogicArray
from cocotb.queue import Queue
from cocotb.triggers import Event, ClockCycles, ReadOnly
from cocotbext.ofm.base.drivers import BusDriver
from cocotbext.ofm.utils.signals import await_signal_sync
from cocotbext.ofm.avmm.config import AvalonMMDataUnits, AvalonMMParams
from cocotbext.ofm.avmm.transaction import AvalonMMWriteRequestTransaction, AvalonMMReadRequestTransaction, AvalonMMReadResponseTransaction, AvalonMMWriteResponseTransaction, AvalonMMResponseValue
from cocotbext.ofm.utils.ram import RAM


class AvalonMMDriverMaster(BusDriver):
    _signals = []
    _optional_signals = ["address", "read", "readdata", "readdatavalid", "write", "writedata", "burstcount", "ready", "waitrequest"]

    def __init__(self, entity, name, clock, array_idx=None, params: Optional[AvalonMMParams] = None, signal_map: Optional[dict] = None, **kwargs):
        # Signal_map maps the Avalon-MM signal name to the name used by the component.
        # Set before super().__init__(), which reads self._optional_signals to build the bus.
        if signal_map is not None:
            defaults = AvalonMMDriverMaster._optional_signals
            unknown = set(signal_map) - set(defaults)
            if unknown:
                raise ValueError(
                    f"signal_map contains unknown Avalon-MM signal name(s): {sorted(unknown)}. "
                    f"Known names: {defaults}")
            # Merged over the defaults, so a map that renames only the signals whose
            # names differ does not drop the rest of the bus.
            self._optional_signals = {**{name: name for name in defaults}, **signal_map}

        super().__init__(entity, name, clock, array_idx, **kwargs)

        self._address_width    : int   = len(self.bus.address) if hasattr(self.bus, "address") else 0
        self._burstcount_width : int   = len(self.bus.burstcount) if hasattr(self.bus, "burstcount") else 0
        self._writedata_width  : int   = len(self.bus.writedata) if hasattr(self.bus, "writedata") else 0
        self._readdata_width   : int   = len(self.bus.readdata) if hasattr(self.bus, "readdata") else 0

        self._write_data_bytes : int   = self._writedata_width // 8
        self._read_data_bytes  : int   = self._readdata_width // 8

        self._response_queue   : Queue = Queue()
        self._request_queue    : Queue = Queue()
        self._read_beats       : Queue = Queue()

        # use default setting of parameters if they are not set by the user
        self._params = params if params is not None else AvalonMMParams()

        self._clear_control_signals()
        self._propagate_control_signals()

        # start the request/response loops
        cocotb.start_soon(self._request_loop())
        cocotb.start_soon(self._response_loop())

        if hasattr(self.bus, "readdatavalid"):
            cocotb.start_soon(self._read_beat_capture_loop())

    async def write(self, address: int, data: bytes, burst_count: Optional[int] = None, sync: bool = True):
        # create write transaction
        transaction = AvalonMMWriteRequestTransaction()
        transaction.address = address
        transaction.data = data
        transaction.burst_count = burst_count

        await self._send_write_request(transaction, sync)

    def send_write_request(self, transaction: AvalonMMWriteRequestTransaction, sync: bool = True) -> None:
        self._request_queue.put_nowait((transaction, sync))

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
        self._request_queue.put_nowait((transaction, sync))

    def _clear_control_signals(self):
        self._address     = LogicArray("X" * self._address_width)
        self._write_data  = LogicArray("X" * self._writedata_width)
        self._burst_count = LogicArray("X" * self._burstcount_width)
        self._read        = 0
        self._write       = 0

    def _propagate_control_signals(self):
        # ready/waitrequest are driven by the slave, the master must only read them
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

    def _address_step(self, word_count: int) -> int:
        return word_count if self._params.addressUnits == AvalonMMDataUnits.words else word_count * self._write_data_bytes

    def _split_to_words(self, data: bytes) -> list[int]:
        return [int.from_bytes(data[i:i + self._write_data_bytes], "little")
                for i in range(0, len(data), self._write_data_bytes)]

    async def _await_slave_accept(self) -> None:
        """Holds the currently driven request until the slave accepts it."""
        if hasattr(self.bus, "ready"):
            await await_signal_sync(self._clk_re, self.bus.ready)
        elif hasattr(self.bus, "waitrequest"):
            await await_signal_sync(self._clk_re, self.bus.waitrequest, 0)

    async def _drive_beat(self, read: int, write: int, address, burst_count, write_data=None) -> None:
        """Drives a single request beat and returns once the slave has accepted it.

        The request stays asserted while the slave is not ready, as required by
        the Avalon-MM specification.
        """
        self._read        = read
        self._write       = write
        self._address     = address
        self._burst_count = burst_count

        if write_data is not None:
            self._write_data = write_data

        self._propagate_control_signals()

        await self._clk_re
        await self._await_slave_accept()

    async def _insert_idles(self) -> None:
        """Pauses the burst for the number of cycles the idle generator asks for.

        Avalon-MM lets a master deassert its request between the beats of a
        burst and continue later. Only the request is dropped, the rest of the
        signals keep their values the way a stalled master pipeline would.
        """
        idles = self._idle_gen.get(self._idle_tr)

        if idles <= 0:
            return

        self._read  = 0
        self._write = 0
        self._propagate_control_signals()

        for _ in range(idles):
            await self._clk_re

        self._idle_gen.put(self._idle_tr, items=idles, end=True)

    async def _write_burst(self, address: int, words: list[int], sync: bool = True) -> None:
        if sync:
            await self._clk_re

        burst_count = len(words)

        for i, word in enumerate(words):
            if i > 0:
                await self._insert_idles()

            if i == 0 or self._params.constantBurstBehavior:
                beat_address, beat_burst = address, burst_count
            else:
                # Avalon-MM defines address and burstcount only for the first beat
                # of a burst; drive them as don't-care unless the master is
                # configured to hold them for the whole burst.
                beat_address = LogicArray("X" * self._address_width)
                beat_burst   = LogicArray("X" * self._burstcount_width)

            await self._drive_beat(read=0, write=1, address=beat_address,
                                   burst_count=beat_burst, write_data=word)

    async def _send_write_request(self, transaction: AvalonMMWriteRequestTransaction, sync: bool = True) -> None:
        assert self._write_data_bytes > 0, "Write interface not present on the bus or is of null width."

        address     : int  = transaction.address
        words       : list[int] = self._split_to_words(transaction.data)
        burst_count : int  = transaction.burst_count if transaction.burst_count is not None else 1

        for index, offset in enumerate(range(0, len(words), burst_count)):
            chunk = words[offset:offset + burst_count]

            # The bursts of one request follow each other without a gap, the way
            # the NDK Avalon-MM masters drive them, so only the first one aligns
            # to a clock edge.
            await self._write_burst(address, chunk, sync=sync and index == 0)

            address += self._address_step(len(chunk))

        self._clear_control_signals()
        self._propagate_control_signals()

    async def _send_read_request(self, transaction: AvalonMMReadRequestTransaction, sync: bool = True):
        if sync:
            await self._clk_re

        burst_count = transaction.burst_count if transaction.burst_count is not None else 1

        # A pipelined slave can return the first beat in the cycle right after the
        # request is accepted, so the response collector must know about the
        # request before the handshake completes.
        self._response_queue.put_nowait(transaction)

        await self._drive_beat(read=1, write=0, address=transaction.address, burst_count=burst_count)

        self._clear_control_signals()
        self._propagate_control_signals()

    async def _wait_for_read_response(self):
        """Times the read beats of a bus without readdatavalid.

        A bus that has readdatavalid is served by _read_beat_capture_loop instead,
        and readLatency/readWaitTime then have no effect on it.
        """
        # fixed read latency
        if self._params.readLatency > 0:
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

    async def _read_beat_capture_loop(self):
        """Collects every read data beat as it appears on the bus.

        Beats are collected independently of the request that produced them, so
        that responses of consecutive pipelined requests are never missed, no
        matter whether they arrive back-to-back or with gaps.
        """
        while True:
            await self._clk_re
            # Reading straight after the edge is not portable: some simulators have
            # propagated the values the edge produces and some have not. ReadOnly
            # runs once the timestep has settled, so every simulator sees the same
            # beat in the same cycle.
            await ReadOnly()

            if self.bus.readdatavalid.value == 1:
                self._read_beats.put_nowait(self.bus.readdata.value.to_bytes(byteorder="little"))

    async def _request_loop(self):
        while True:
            transaction, sync = await self._request_queue.get()

            if isinstance(transaction, AvalonMMWriteRequestTransaction):
                await self._send_write_request(transaction, sync)
            else:
                await self._send_read_request(transaction, sync)

    async def _response_loop(self):
        while True:
            request = await self._response_queue.get()

            beats = request.burst_count if request.burst_count is not None else 1
            data  = b""

            for _ in range(beats):
                if hasattr(self.bus, "readdatavalid"):
                    data += await self._read_beats.get()
                else:
                    await self._wait_for_read_response()
                    data += self.bus.readdata.value.to_bytes(byteorder="little")

            request.response.data = data

            if request.event is not None:
                request.event.set()


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
