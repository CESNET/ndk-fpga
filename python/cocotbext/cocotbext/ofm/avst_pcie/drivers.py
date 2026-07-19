# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2024-2026 CESNET z. s. p. o.
# Author(s): Radek Isa <isa@cesnet.cz>
#            Daniel Kondys <kondys@cesnet.cz>
#            Martin Spinler <spinler@cesnet.cz>

import random
from typing import Any

import cocotb
from cocotb.triggers import RisingEdge
from cocotbext.ofm.base.drivers import BusDriver
from cocotb.queue import Queue
from cocotb.handle import Immediate

from cocotbext.ofm.pcie.AvstRequester import CompletionHeaderEmpty as RcHdrEmpty
from cocotbext.ofm.pcie.AvstCompleter import RequestHeaderEmpty as CqHdrEmpty
from cocotbext.ofm.utils import concat
from cocotbext.ofm.base.transaction import IdleTransaction


class AvstPcieDriverMaster(BusDriver):
    _signals = ["DATA", "HDR", "SOP", "EOP", "EMPTY", "VALID", "READY"]
    _optional_signals = ["PREFIX", "BAR_RANGE"]

    def __init__(self, entity, name, clock, array_idx=None):
        super().__init__(entity, name, clock, array_idx=array_idx)
        self._cq_q = Queue()
        self._rc_q = Queue()
        self._re = RisingEdge(self.clock)

        self._ready_latency = 27
        self.current_ready_latency = 0

        if self._ready_latency == 0:
            self._write = self._write_rl_0
        else:
            self._write = self._write_rl

        ms, os = self._signals, self._optional_signals
        signals = ms | os if isinstance(ms, dict) else ms + os
        self._word = {}
        self._segs = len(self.bus.VALID)
        for s in signals:
            if hasattr(self.bus, s) and s not in ["READY"]:
                getattr(self.bus, s).set(Immediate(0))
                self._word[s] = 0

        self._empty_width = len(self.bus.EMPTY) // self._segs
        self._hdr_width = len(self.bus.HDR) // self._segs
        self._avst_width = (len(self.bus.DATA) // 8) // self._segs
        self._seg_current = 0

        cocotb.start_soon(self.send_transaction())

    def _clear_control_signals(self):
        for sig in self._word:
            setattr(self.bus, sig, 0)

    def prep_words(self, tr, send):
        data, hdr, hdr_empty = tr
        tr_words = []
        orig_data_len = len(data)
        end = False
        while not end:
            length = min(self._avst_width, len(data))
            begin = len(data) == orig_data_len
            end = len(data) == length

            self._word["DATA"] |= concat(list(zip(data[:length], [8] * length))) << (self._seg_current * self._avst_width * 8)
            self._word["EMPTY"] |= (((self._avst_width - length) // 4) if length else 0) << (self._seg_current * self._empty_width)
            self._word["HDR"] |= (hdr.serialize() if begin else hdr_empty.serialize()) << (self._seg_current * self._hdr_width)
            self._word["SOP"] |= (1 if begin else 0) << self._seg_current
            self._word["EOP"] |= (1 if end else 0) << self._seg_current

            self._seg_current += 1
            data = data[length:]
            if self._seg_current == self._segs:
                self._word["VALID"] = 2**self._segs - 1
                tr_words.append(self._word)
                self._word = dict.fromkeys(self._word, 0)
                self._seg_current = 0
            elif end:
                if send: # Send words even if the last word is incomplete
                    self._word["VALID"] = 2**self._seg_current - 1
                    tr_words.append(self._word)
                    self._word = dict.fromkeys(self._word, 0)
                    self._seg_current = 0
                # else: Send all without the last incomplete word, which is kept as is (in self._word)

        return tr_words

    async def send_transaction(self):
        queue_select = None

        while True:
            # The algorithm below ensures that when data in queues are in words
            # (not whole transactions). Only data from one queue between SOF
            # and EOF are sent (doesn't allow for words of different
            # transactions to mix).
            if queue_select is None:
                # Selecting QUEUE for data
                # Randomly select priority to prevent starvation
                priority_queue = random.choice([0, 1])
                if not self._cq_q.empty() and (priority_queue == 0 or self._rc_q.empty()):
                    queue_select = self._cq_q
                if not self._rc_q.empty():
                    queue_select = self._rc_q

            # Both queue is empty
            if queue_select is None or queue_select.empty():
                await self._re
            else:
                tr = queue_select.get_nowait()
                send = self._cq_q.empty() and self._rc_q.empty()
                data_words = self.prep_words(tr, send)
                for word in data_words:
                    await self._write(word)
                else:
                    await self._re

            queue_select = None

    async def _write_data(self, data):
        for signal, value in data.items():
            getattr(self.bus, signal).value = value
        await self._re

    async def _write_rl(self, data):
        """
        Write data on the interface when ready latency is not zero.
        """
        #Check if data can be put into interface
        if not self.bus.READY.value:
            if self.current_ready_latency == 0:
                while not self.bus.READY.value:
                    await self._re
            else:
                self.current_ready_latency -= 1
        else:
            self.current_ready_latency = self._ready_latency

        await self._write_data(data)
        self.bus.VALID.value = 0

    async def _write_rl_0(self, data):
        """
        Write data on interface when ready latency is zero
        In this case interface behaves simular to MFB
        """

        self.bus.VALID.value = 1
        await self._write_data(data)

        for signal, value in data.items():
            if signal != "":
                getattr(self.bus, signal).value = value

        await self._re
        while not self.bus.READY.value:
            await self._re

        self.bus.VALID.value = 0

    async def _driver_send(self, transaction: Any, sync: bool = True, **kwargs: Any):
        """
        Writes idle transaction to the bus or passes valid transaction to the write method.
        """

        # handle idle transaction
        if isinstance(transaction, IdleTransaction):
            self._clear_control_signals()
            await self._clk_re
        # handle valid transaction
        else:
            try:
                hdr, data, tr_type = transaction
            except (ValueError, TypeError) as e:
                raise ValueError("Transaction must be an iterable with exactly 3 items: (hdr, data, tr_type)") from e

            match tr_type:
                case 0:  # CQ transaction
                    hdr_empty = CqHdrEmpty()
                    self._cq_q.put_nowait((data, hdr, hdr_empty))
                case 1:  # RC transaction
                    hdr_empty = RcHdrEmpty()
                    self._rc_q.put_nowait((data, hdr, hdr_empty))
                case _:
                    raise NotImplementedError(f"Unknown transaction type: {tr_type}")

    async def _send_thread(self) -> None:
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


class AvstPcieDriverSlave(BusDriver):
    _signals = ["VALID", "READY"]

    def __init__(self, entity, name, clock, array_idx=None):
        super().__init__(entity, name, clock, array_idx=array_idx)

        self.bus.READY.set(Immediate(1))
