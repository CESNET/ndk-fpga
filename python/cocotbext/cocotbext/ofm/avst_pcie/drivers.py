import random

import cocotb
from cocotb.triggers import RisingEdge
from cocotb_bus.drivers import BusDriver
from cocotb.queue import Queue


class AvstPcieDriverMaster(BusDriver):
    _signals = ["DATA", "HDR", "SOP", "EOP", "EMPTY", "VALID", "READY"]
    _optional_signals = ["PREFIX", "BAR_RANGE"]

    def __init__(self, entity, name, clock, array_idx=None):
        BusDriver.__init__(self, entity, name, clock, array_idx=array_idx)
        self._cq_q = Queue()
        self._rc_q = Queue()
        self._re = RisingEdge(self.clock)
        self._ready_latency = 27
        self.current_ready_latency = 0
        self.in_frame = False

        if self._ready_latency == 0:
            self._write = self._write_rl_0
        else:
            self._write = self._write_rl

        ms, os = self._signals, self._optional_signals
        signals = ms | os if isinstance(ms, dict) else ms + os
        for s in signals:
            if hasattr(self.bus, s) and s not in ["READY"]:
                getattr(self.bus, s).setimmediatevalue(0)

        cocotb.start_soon(self.send_transaction())

    async def write_cq(self, data):
        self._cq_q.put_nowait(data)

    async def write_rc(self, data):
        self._rc_q.put_nowait(data)

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
                data = queue_select.get_nowait()
                await self._write(data)

            if not self.in_frame:
                queue_select = None

    async def _write_data(self, data):
        for signal, value in data.items():
            if signal != "":
                region_mask = 0x1
                for region in range(len(self.bus.SOP)):
                    if signal == "EOP" and (value & region_mask) != 0:
                        self.in_frame = False
                    if signal == "SOP" and (value & region_mask) != 0:
                        self.in_frame = True
                    region_mask <<= 1
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


class AvstPcieDriverSlave(BusDriver):
    _signals = ["VALID", "READY"]

    def __init__(self, entity, name, clock, array_idx=None):
        BusDriver.__init__(self, entity, name, clock, array_idx=array_idx)

        self.bus.READY.setimmediatevalue(1)
