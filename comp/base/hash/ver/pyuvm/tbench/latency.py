# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from pyuvm import uvm_subscriber, uvm_tlm_analysis_fifo, ConfigDB
from cocotb.triggers import RisingEdge


class Latency(uvm_subscriber):
    def build_phase(self):
        self._latency : int = 0

        self._dut = ConfigDB().get(None, "", "DUT")
        self._key_queue  = uvm_tlm_analysis_fifo("key_queue", self)
        self._hash_queue = uvm_tlm_analysis_fifo("hash_queue", self)

        self.key_export  = self._key_queue.analysis_export
        self.hash_export = self._hash_queue.analysis_export

    async def run_phase(self):
        # waiting for the first key to be sent
        await self._key_queue.get()

        # waiting for the first hash to be received and counting clock cycles
        while not self._hash_queue.can_get():
            await RisingEdge(self._dut.clock)
            self._latency += 1

    def report_phase(self):
        self.logger.info(f"Latency is {self._latency} clock cycles.")
