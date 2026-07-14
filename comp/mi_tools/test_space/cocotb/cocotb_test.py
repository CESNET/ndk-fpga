# cocotb_test.py:
# Copyright (C) 2024-2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import cocotb
import logging
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotbext.ofm.mi.drivers import MIRequestDriver as MIDriver
from cocotbext.ofm.ver.generators import random_packets
from cocotb_bus.scoreboard import Scoreboard


class testbench():
    def __init__(self, dut, debug=False):
        self.dut = dut
        self.stream_in = MIDriver(dut, "MI", dut.CLK)

        # Create a scoreboard on the stream_out bus
        self.pkts_sent = 0
        self.expected_output = []
        self.scoreboard = Scoreboard(dut)

        if debug:
            self.stream_in.log.setLevel(logging.DEBUG)

    def model(self, transaction):
        """Model the DUT based on the input transaction"""
        self.expected_output.append(transaction)
        self.pkts_sent += 1

    async def reset(self):
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 2)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)


@cocotb.test()
async def run_test(dut, pkt_count=5000, item_width_min=1, item_width_max=32):
    # Start clock generator
    cocotb.start_soon(Clock(dut.CLK, 5, unit='ns').start())
    tb = testbench(dut)
    await tb.reset()

    cocotb.log.info("\nREAD AND WRITE TEST\n")

    for transaction in random_packets(item_width_min, item_width_max, pkt_count):
        cocotb.log.debug(f"generated transaction: {transaction.hex()}")
        await tb.stream_in.write(int.from_bytes(transaction[0:4], 'little'), transaction)
        output = await tb.stream_in.read(int.from_bytes(transaction[0:4], 'little'), len(transaction))
        cocotb.log.debug(f"received transaction: {output.hex()}")

        assert output == transaction

    cocotb.log.info("DONE")

    raise tb.scoreboard.result
