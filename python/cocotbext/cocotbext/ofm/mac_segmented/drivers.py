# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from cocotbext.ofm.base.drivers import BusDriver
from cocotbext.ofm.utils.signals import await_signal_sync, set_signal_delayed
from cocotbext.ofm.utils.binary import Binary, BinaryVector
from copy import copy
from random import randint
from cocotb.triggers import Event


class MAC_Segmented_RX_Driver(BusDriver):
    _signals = ["data", "valid", "inframe", "eop_empty", "fcs_error", "error", "status"]

    def __init__(self, entity, name, clock, ready_sig=None, array_idx=None) -> None:
        super().__init__(entity, name, clock, array_idx=array_idx)
        self._bus_width = len(self.bus.data) // 8  # data width in bytes
        self._segments = len(self.bus.inframe)
        self._segment_width = self._bus_width // self._segments  # segment width in bytes
        self._ready = ready_sig
        self.frame_cnt = 0

        self._init_control_signals()
        self._propagate_control_signals()

    def _init_control_signals(self) -> None:
        self._segment_offset: int = 0
        self._eop_found: bool = False

        self._data: BinaryVector = BinaryVector(item_count=self._segments, item_bits=self._segment_width * 8)
        self._in_frame: Binary = Binary(bits=self._segments)
        self._eop_empty: BinaryVector = BinaryVector(item_count=self._segments, item_bits=3)

        # unused, implementation may be added in the future
        self._fcs_error: Binary = Binary(bits=self._segments)
        self._mac_error: BinaryVector = BinaryVector(item_count=self._segments, item_bits=2)
        self._status_data: BinaryVector = BinaryVector(item_count=self._segments, item_bits=3)

    def _clear_control_signals(self) -> None:
        """Sets control signals to default values without sending them to the bus."""
        self._segment_offset = 0
        self._eop_found = False
        self._data.value = 0
        self._in_frame.value = 0
        self._eop_empty.value = 0
        self._fcs_error.value = 0
        self._mac_error.value = 0
        self._status_data.value = 0

    def _propagate_control_signals(self) -> None:
        """Sends value of control signals to the bus."""

        # data on the MAC Segmented bus is sent in reverse order
        self.bus.data.value = self._data.flipped_endian().int
        self.bus.inframe.value = self._in_frame.reversed().int
        self.bus.eop_empty.value = self._eop_empty.vreversed().int
        self.bus.fcs_error.value = self._fcs_error.reversed().int
        self.bus.error.value = self._mac_error.vreversed().int
        self.bus.status.value = self._status_data.vreversed().int

    async def _move_frame(self) -> None:
        # deasserting vld signal if the bus is not ready
        await self._clk_re

        if self._ready is not None:
            self.bus.valid.value = 0 if not self._ready else self.bus.valid.value

            # awaiting assertion of ready signal before proceding
            await await_signal_sync(self._clk_re, self._ready)

            # if vld has been deactivated, it is reactivated in 1 to 8 cycles
            if self.bus.valid.value == 0:
                await set_signal_delayed(self._clk_re, self.bus.valid, delay=randint(1, 8), value=1)

        else:
            self.bus.valid.value = 1

        self._propagate_control_signals()
        self._clear_control_signals()

    async def _driver_send(self, transaction: bytes, sync: bool = True) -> None:
        # creating internal copy of the transaction so the external one isn't being edited
        data = copy(transaction)

        self.log.debug(f"transaction: {data.hex()}")

        width: int = self._segment_width

        while data:
            offset: int = self._segment_offset

            # asserting in frame for the next cycle, but it may be deasserted if it's EOP
            self._in_frame[offset] = 1

            if len(data) <= width:
                # setting _eop_empty of the current segment to number of unused bytes
                self._eop_empty[offset] = width - len(data)
                # appending empty bytes to a transaction slice shorter than a segment
                data += b'\0' * (width - len(data))
                # EOP is in this segment, deasserting _in_frame
                self._in_frame[offset] = 0

            self._data[offset] = data[:width]

            # cutting off part of transaction that was sent
            data = data[width:]

            self._segment_offset += 1

            # sending the filled up segments to the bus
            if self._segment_offset * width >= self._bus_width:
                await self._move_frame()

    async def write_packet(self, data: bytes | list, sync: bool = True):
        """
        deprecated::
            Use the Bus.append() instead.
        """

        e = Event()
        if isinstance(data, list):
            data = bytes(data)
        self.append(data, event=e)
        await e.wait()

    async def _send_thread(self):
        while True:
            # Sleep until we have something to send
            while not self._sendQ:
                self._pending.clear()
                await self._pending.wait()

            while self._sendQ:
                transaction, callback, event, kwargs = self._sendQ.popleft()
                await self._send(transaction, callback=callback, event=event, sync=False, **kwargs)
                self.frame_cnt += 1
                # Notify the world that this transaction is complete
                if event:
                    event.set()
                if callback:
                    callback(transaction)

            await self._move_frame()
            await self._move_frame()
