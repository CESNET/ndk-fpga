from typing import Any

from cocotb.triggers import Event

from ..base.drivers import BusDriver
from ..base.transaction import IdleTransaction


class AvstEthDriver(BusDriver):
    _signals = ["data", "valid", "sop", "eop", "empty", "error"]
    # _optional_signals = ["status_valid", "status_data", "pause", "pfc"]

    def __init__(self, entity, name, clock, array_idx=None):
        super().__init__(entity, name, clock, array_idx=array_idx)

        self._bus_width = len(self.bus.data) // 8
        self._bus_segments = len(self.bus.valid)
        self._bus_segment_width = self._bus_width // self._bus_segments

        self._cfg_update(
            bits_per_word=len(self.bus.data),
        )

        self.clear_control_signals()

    def clear_control_signals(self):
        self.bus.valid.value = 0
        self.bus.sop.value = 0
        self.bus.eop.value = 0
        self.bus.empty.value = 0
        self.bus.error.value = 0

        self._vld = 0
        self._sop = 0
        self._eop = 0
        self._emp = 0
        self._err = 0

    def propagate_control_signals(self):
        self.bus.valid.value = self._vld
        self.bus.sop.value = self._sop
        self.bus.eop.value = self._eop
        self.bus.empty.value = self._emp
        self.bus.error.value = self._err

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
                idle_count = self._idle_gen.get(transaction) // self._bus_width
                if idle_count == 0:
                    break

                for _ in range(idle_count):
                    await self._send(self._idle_tr, callback=None, event=event, sync=False, **kwargs)

            await self._send(transaction, callback=callback, event=event, sync=False, **kwargs)

    async def _driver_send(self, transaction: Any, sync: bool = True, **kwargs: Any) -> None:
        clk_re = self._clk_re
        if isinstance(transaction, IdleTransaction):
            await clk_re
            self.clear_control_signals()
            self._idle_gen.put(transaction, items=self._bus_width)
            return
        elif isinstance(transaction, bytes):
            data = memoryview(transaction)
        else:
            raise NotImplementedError

        assert len(data)

        items = self._bus_width
        end = False
        empty_items = 0

        self._sop = 1

        while data:
            self._vld = 1

            # TODO: ability to send 2 packets in one word
            if len(data) <= self._bus_width:
                end = True
                items = len(data)
                empty_items = self._bus_width - items

                if items <= self._bus_segment_width:
                    self._eop = 1
                    self._emp = self._bus_segment_width - items
                else:
                    self._eop = 2
                    self._emp = empty_items

            self.bus.data.value = int.from_bytes(data[0:items], byteorder="big") << (empty_items) * 8
            data = data[items:]

            self.propagate_control_signals()
            await clk_re
            self.clear_control_signals()

            self._idle_gen.put(transaction, items=items, end=end)
            if empty_items:
                self._idle_gen.put(self._idle_tr, items=empty_items)
