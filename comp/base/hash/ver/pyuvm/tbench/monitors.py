# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from pyuvm import uvm_monitor, uvm_analysis_port
from cocotb.triggers import Event
from cocotb.queue import Queue


class HashUVMMonitor(uvm_monitor):
    def build_phase(self):
        self.ap = uvm_analysis_port("ap", self)
        self._recv_queue = Queue()
        self._pending = Event(name="Monitor._pending")

    def start_of_simulation_phase(self):
        self.parent.dut.monitor.add_callback(self._monitor_callback)

    async def run_phase(self):
        while True:
            while self._recv_queue.empty():
                self._pending.clear()
                await self._pending.wait()

            while not self._recv_queue.empty():
                transaction = self._recv_queue.get_nowait()
                self.ap.write(transaction)

    def _monitor_callback(self, transaction):
        self._recv_queue.put_nowait(transaction)
        self._pending.set()
