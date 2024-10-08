from typing import Any

from cocotb.triggers import Event

from ..base.drivers import BusDriver
from ..base.transaction import IdleTransaction

#def byte_deserialize(data):
#    return reduce(operator.or_, [(data[i] & 0xff) << (8*i) for i in range(len(data))])


class LBusDriver(BusDriver):
    _signals = ["data", "ena", "sop", "eop", "err", "mty"]

    def __init__(self, entity, name, clock, array_idx=None):
        super().__init__(entity, name, clock, array_idx=array_idx)
        self._segments = len(self.bus.data)
        self._bytes_per_item = len(self.bus.data[0]) // 8

        self._cfg_update(
            bits_per_word=self._bytes_per_item * 8 * self._segments
        )
        self._next_segment = 0
        self.clear_control_signals()

    def clear_control_signals(self):
        self.bus.sop.value = 0
        self.bus.eop.value = 0
        self.bus.ena.value = 0
        self.bus.err.value = 0

        for i in range(self._segments):
            self.bus.mty[i].value = 0

        self._ena = 0
        self._sop = 0
        self._eop = 0
        self._mty = [0] * self._segments

    def propagate_control_signals(self):
        self.bus.ena.value = self._ena
        self.bus.sop.value = self._sop
        self.bus.eop.value = self._eop
        for i in range(self._segments):
            self.bus.mty[i].value = self._mty[i]

    async def write_packet(self, data, sync=True):
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
        await self._clk_re
        if self._cfg.get("clk_freq") is None:
            await self._measure_clkfreq(self._clk_re)

        while True:
            if self._sendQ:
                transaction, callback, event, kwargs = self._sendQ.popleft()
            else:
                transaction, callback, event, kwargs = self._idle_tr, None, None, {}

            while True:
                idle_count = self._idle_gen.get(transaction) // self._bytes_per_item

                if idle_count == 0:
                    break
                for _ in range(idle_count):
                    await self._send(self._idle_tr, callback=None, event=event, sync=False, **kwargs)

            await self._send(transaction, callback=callback, event=event, sync=False, **kwargs)

    async def _driver_send(self, transaction: Any, sync: bool = True, **kwargs: Any) -> None:
        clk_re = self._clk_re

        if isinstance(transaction, IdleTransaction):
            self._idle_gen.put(transaction, items=self._bytes_per_item)
            self._next_segment = (self._next_segment + 1) % self._segments
            if self._next_segment == 0:
                await clk_re
                self.clear_control_signals()
            return
        #elif isinstance(transaction, list):
        #    data = memoryview(bytes(transaction))
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
                nbytes = len(data)

            self.bus.data[i].value = int.from_bytes(data[0:nbytes], byteorder="big") << (empty_items * 8)

            data = data[nbytes:]
            self._next_segment = (self._next_segment + 1) % self._segments

            self.propagate_control_signals()
            if self._next_segment == 0:
                await clk_re
                self.clear_control_signals()

            self._idle_gen.put(transaction, items=nbytes, end=(len(data) == 0))
            if empty_items:
                self._idle_gen.put(self._idle_tr, items=empty_items)
