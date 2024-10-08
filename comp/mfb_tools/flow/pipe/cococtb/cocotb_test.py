# cocotb_test.py:
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): David Beneš <xbenes52@vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import itertools
import random

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotbext.ofm.mfb.drivers import MFBDriver
from cocotbext.ofm.mfb.monitors import MFBMonitor
from cocotbext.ofm.ver.generators import random_packets
from cocotb_bus.drivers import BitDriver
from cocotb_bus.scoreboard import Scoreboard


class testbench():
    def __init__(self, dut):
        self.dut = dut
        self.RX_MFB = MFBDriver(dut, "RX", dut.CLK)
        self.backpressure = BitDriver(dut.TX_DST_RDY, dut.CLK)
        self.TX_MFB = MFBMonitor(dut, "TX", dut.CLK)

        # Create a scoreboard on the TX_MFB bus
        self.expected_output = []
        self.scoreboard = Scoreboard(dut)
        self.scoreboard.add_interface(self.TX_MFB, self.expected_output)

    def model(self, transaction):
        """Model the DUT based on the input transaction"""
        self.expected_output.append(transaction)

    async def reset(self):
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 2)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)


@cocotb.test()
async def run_test(dut, pkt_count=10000, frame_size_min=60, frame_size_max=512):
    # Start clock generator
    cocotb.start_soon(Clock(dut.CLK, 5, units='ns').start())
    tb = testbench(dut)
    await tb.reset()
    #That's not really a random number, is it?
    # tb.backpressure.start((1, i % 5) for i in itertools.count())
    tb.backpressure.start((1, random.randint(0, 5)) for i in itertools.count())

    for transaction in random_packets(frame_size_min, frame_size_max, pkt_count):
        tb.model(transaction)
        # print("generated transaction: " + transaction.hex())
        tb.RX_MFB.append(transaction)

    last_num = 0
    while (tb.TX_MFB.frame_cnt < pkt_count):
        if (tb.TX_MFB.frame_cnt // 1000) > last_num:
            last_num = tb.TX_MFB.frame_cnt // 1000
            cocotb.log.info("Number of transactions processed: %d/%d" % (tb.TX_MFB.frame_cnt, pkt_count))
        await ClockCycles(dut.CLK, 100)

    await ClockCycles(dut.CLK, 100)
    # print("RX: %d/%d" % (tb.RX_MFB.frame_cnt, pkt_count))
    # print("TX: %d/%d" % (tb.TX_MFB.frame_cnt, pkt_count))

    raise tb.scoreboard.result
