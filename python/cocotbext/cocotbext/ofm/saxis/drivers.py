# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 DynaNIC Semiconductors ltd.
# Author(s): Vlastimil Kosar <kosar@dyna-nic.com>

import random
from typing import Any

from ..lbus.drivers import LBusDriver
from ..base.transaction import IdleTransaction


class SAXISDriver(LBusDriver):
    """Driver of the Segmented AXI-Stream of the AMD DCMAC (PG369), 128-bit segments.

    Frames are written to consecutive segments, a frame starts in the segment
    following the end of the previous one. The first byte of a segment is in
    the bits 7:0 of its data.

    Args:
        idle_mode: "segment" - every idle item disables one segment, so a frame
                   can start in any segment and gaps between frames occur
                   inside a cycle (beyond what PG369 allows on RX).
                   "cycle" - idles are whole cycles with VALID low and the
                   rest of a started cycle stays disabled, as required by PG369.
        inner_gap_prob: probability of idle cycles (VALID low) inserted after
                   a cycle in the middle of a frame, as the DCMAC RX does.
        inner_gap_max: maximum number of idle cycles of one such gap.

    The ``err`` keyword of :meth:`append` sets ERR in the last segment of the frame.
    """

    _signals = ["data", "ena", "sop", "eop", "err", "mty", "valid"]

    def __init__(self, entity, name, clock, array_idx=None, idle_mode: str = "segment",
                 inner_gap_prob: float = 0.0, inner_gap_max: int = 3):
        if idle_mode not in ("segment", "cycle"):
            raise ValueError(f"Unsupported idle_mode {idle_mode}")
        self._idle_mode = idle_mode
        self._inner_gap_prob = inner_gap_prob
        self._inner_gap_max = inner_gap_max
        self.frame_cnt = 0
        super().__init__(entity, name, clock, array_idx=array_idx)

    def clear_control_signals(self):
        self.bus.sop.value   = 0
        self.bus.eop.value   = 0
        self.bus.ena.value   = 0
        self.bus.err.value   = 0
        self.bus.valid.value = 0

        for i in range(self._segments):
            self.bus.mty[i].value = 0

        self._ena = 0
        self._sop = 0
        self._eop = 0
        self._err = 0
        self._mty = [0] * self._segments

    def propagate_control_signals(self):
        self.bus.ena.value = self._ena
        self.bus.sop.value = self._sop
        self.bus.eop.value = self._eop
        self.bus.err.value = self._err
        for i in range(self._segments):
            self.bus.mty[i].value = self._mty[i]
        if self._ena > 0:
            self.bus.valid.value = 1
        else:
            self.bus.valid.value = 0

    async def _send_idle(self, transaction: IdleTransaction) -> None:
        clk_re = self._clk_re

        if self._idle_mode == "segment":
            self._idle_gen.put(transaction, items=self._bytes_per_item)
            self._next_segment = (self._next_segment + 1) % self._segments
            if self._next_segment == 0:
                await clk_re
                self.clear_control_signals()
            return

        free_segments = self._segments - self._next_segment
        self._idle_gen.put(transaction, items=self._bytes_per_item * free_segments)
        self._next_segment = 0
        await clk_re
        self.clear_control_signals()

    async def _driver_send(self, transaction: Any, sync: bool = True, err: bool = False, **kwargs: Any) -> None:
        clk_re = self._clk_re

        if isinstance(transaction, IdleTransaction):
            await self._send_idle(transaction)
            return
        elif isinstance(transaction, bytes):
            data = memoryview(transaction)
        else:
            raise NotImplementedError

        assert len(data)

        datalen = len(data)
        bpi = self._bytes_per_item
        empty_items = 0
        nbytes = bpi

        while data:
            i = self._next_segment

            self._ena |= 1 << i
            if len(data) == datalen:
                self._sop |= 1 << i

            if len(data) <= bpi:
                empty_items = bpi - len(data)
                self._mty[i] = empty_items

                self._eop |= 1 << i
                if err:
                    self._err |= 1 << i
                nbytes = len(data)

            self.bus.data[i].value = int.from_bytes(data[0:nbytes], byteorder="little")

            data = data[nbytes:]
            self._next_segment = (self._next_segment + 1) % self._segments

            self.propagate_control_signals()
            if self._next_segment == 0:
                await clk_re
                self.clear_control_signals()
                if data and random.random() < self._inner_gap_prob:
                    for _ in range(random.randint(1, self._inner_gap_max)):
                        await clk_re

            self._idle_gen.put(transaction, items=nbytes, end=(len(data) == 0))
            if empty_items:
                self._idle_gen.put(self._idle_tr, items=empty_items)

        self.frame_cnt += 1
