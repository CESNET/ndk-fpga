# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025-2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

import cocotb
from pyuvm import uvm_scoreboard, uvm_tlm_analysis_fifo, uvm_get_port
from cocotbext.ofm.utils.math import ceildiv, bitmask


class Scoreboard(uvm_scoreboard):
    def build_phase(self):
        self.trans_cnt = 0
        self.errors = 0

        self._expected_queue = uvm_tlm_analysis_fifo("expected_queue", self)
        self._result_queue   = uvm_tlm_analysis_fifo("result_queue", self)
        self._expected_port  = uvm_get_port("expected_port", self)
        self._result_port    = uvm_get_port("result_port", self)
        self.expected_export = self._expected_queue.analysis_export
        self.result_export   = self._result_queue.analysis_export

    def connect_phase(self):
        self._expected_port.connect(self._expected_queue.get_export)
        self._result_port.connect(self._result_queue.get_export)

    def check_phase(self):
        key_width_bytes  = ceildiv(8, self.parent.dut.key_width)
        seed_width_bytes = ceildiv(8, self.parent.dut.seed_width)
        hash_width = self.parent.dut.hash_width

        while self._expected_port.can_get():
            _, expected_seq  = self._expected_port.try_get()
            got_success, got = self._result_port.try_get()

            if not got_success:
                self.logger.error("Not all expected transactions have been received.")
                self.errors += 1
                return

            hash = self.parent.dut.hash(expected_seq.key.to_bytes(key_width_bytes, "little"), expected_seq.seed.to_bytes(seed_width_bytes, "little"))

            expected = dict()
            expected["hash"] = hash & bitmask(hash_width)
            expected["meta"] = expected_seq.meta

            if expected != got:
                self.logger.error(f"FAILED: expected {expected}, but got {got}.")
                self.errors += 1

            self.trans_cnt += 1

        if self._result_port.can_get():
            self.logger.error("Got a transaction, but expected nothing.")
            self.errors += 1

    def report_phase(self):
        self.logger.info(f"All {self.trans_cnt} transactions processed.")

    def final_phase(self):
        assert self.errors == 0, f"{self.errors} errors found, test failed."
        cocotb.pass_test()
