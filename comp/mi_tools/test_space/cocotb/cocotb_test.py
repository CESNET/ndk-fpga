# cocotb_test.py:
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <Ondrej.Schwarz@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotbext.ofm.mi.drivers import MIMasterDriver as MIDriver
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
            self.stream_in.log.setLevel(cocotb.logging.DEBUG)

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
async def run_test(dut, pkt_count=1000, item_width_min=1, item_width_max=32):
    # Start clock generator
    cocotb.start_soon(Clock(dut.CLK, 5, units='ns').start())
    tb = testbench(dut)
    await tb.reset()

    cocotb.log.info("\nREAD32 AND WRITE32 TEST\n")

    for transaction in random_packets(4, 4, pkt_count):
        cocotb.log.debug(f"generated transaction: {transaction.hex()}")
        await tb.stream_in.write32(int.from_bytes(transaction, 'little'), transaction)
        output = await tb.stream_in.read32(int.from_bytes(transaction, 'little'))
        cocotb.log.debug(f"recieved transaction: {output.hex()}")

        assert output == transaction

    cocotb.log.info("DONE")

    cocotb.log.info("\nREAD AND WRITE TEST\n")

    for transaction in random_packets(item_width_min, item_width_max, pkt_count):
        cocotb.log.debug(f"generated transaction: {transaction.hex()}")
        await tb.stream_in.write(int.from_bytes(transaction[0:4], 'little'), transaction)
        output = await tb.stream_in.read(int.from_bytes(transaction[0:4], 'little'), len(transaction))
        cocotb.log.debug(f"recieved transaction: {output.hex()}")

        assert output == transaction

    cocotb.log.info("DONE")

    cocotb.log.info("\nREAD64 AND WRITE64 TEST\n")

    for transaction in random_packets(8, 8, pkt_count):
        cocotb.log.debug(f"generated transaction: {transaction.hex()}")
        await tb.stream_in.write64(int.from_bytes(transaction[0:4], 'little'), transaction)
        output = await tb.stream_in.read64(int.from_bytes(transaction[0:4], 'little'))
        cocotb.log.debug(f"recieved transaction: {output.hex()}")

        assert output == transaction

    cocotb.log.info("DONE")

    raise tb.scoreboard.result
