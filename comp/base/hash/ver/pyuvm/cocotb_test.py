# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

import pyuvm
import cocotb
from pyuvm import uvm_test, uvm_root, ConfigDB
from cocotb.triggers import ClockCycles
from dut import HashDUT
from tbench.env import HashEnv
from tbench.sequences import TestHashSequencesBase, TestHashSequencesAll, TestHashSequencesConstSeed
from random import randint


class BaseTest(uvm_test):
    def build_phase(self):
        self.dut = HashDUT("dut", self)
        ConfigDB().set(None, "*", "DUT", self.dut)
        self.env = HashEnv("env", self)

    def start_of_simulation_phase(self):
        self.test = TestHashSequencesBase("test", min_items=1, max_items=512, seq_count=1000, min_empty=0, max_empty=512)

    async def run_phase(self):
        self.raise_objection()
        await self.test.start()

        await ClockCycles(self.env.dut.clock, 100)

        last_num = 0

        while self.dut.monitor.trans_cnt < self.test.item_count:
            if (self.dut.monitor.trans_cnt // 1000) > last_num:
                last_num = self.dut.monitor.trans_cnt // 1000
                self.logger.info(f"Number of transactions tb.stream_out.trans_cnt: {self.dut.monitor.trans_cnt}/{self.test.item_count}")
            await ClockCycles(self.env.dut.clock, 100)

        self.drop_objection()


@pyuvm.test()
class TestAll(BaseTest):
    """Tests all sequences."""

    def start_of_simulation_phase(self):
        self.test = TestHashSequencesAll("test", min_items=1, max_items=256, seq_count=1000, min_empty=0, max_empty=256)


@pyuvm.test()
class TestEffectivity(BaseTest):
    """Test designed to detect collisions and inconsistencies."""

    def start_of_simulation_phase(self):
        seed = randint(0, 2**self.dut.seed_width-1)
        self.test = TestHashSequencesConstSeed("test", min_items=1, max_items=1, seq_count=100_000, min_empty=0, max_empty=0, const_seed=seed)


@pyuvm.test()
class TestLatency(BaseTest):
    """Test designed to only test latency. One key is sent, one hash is generated."""

    def start_of_simulation_phase(self):
        self.test = TestHashSequencesAll("test", min_items=1, max_items=1, seq_count=1, min_empty=0, max_empty=0)


# cocotb wrappers so test to be run can be selected via the TESTCASE environment variable
@cocotb.test(skip=True)
async def run_test_all(dut):
    await uvm_root().run_test("TestAll", dut)


@cocotb.test(skip=True)
async def run_test_effectivity(dut):
    await uvm_root().run_test("TestEffectivity", dut)


@cocotb.test(skip=True)
async def run_test_latency(dut):
    await uvm_root().run_test("TestLatency", dut)
