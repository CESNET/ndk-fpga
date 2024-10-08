# cocotb_test.py: MI Pipe test
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <Ondrej.Schwarz@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from drivers import MIMasterDriverTB as MIMasterDriver
from drivers import MISlaveDriverTB as MISlaveDriver
from cocotbext.ofm.mi.monitors import MIMasterMonitor, MISlaveMonitor
from cocotbext.ofm.ver.generators import random_packets
from cocotb_bus.drivers import BitDriver
from cocotb_bus.scoreboard import Scoreboard

import itertools


class testbench():
    def __init__(self, dut, debug=False):
        self.dut = dut
        self.master_stream_in = MIMasterDriver(dut, "IN", dut.CLK)
        self.master_stream_out = MIMasterMonitor(dut, "OUT", dut.CLK)
        self.slave_stream_in = MISlaveDriver(dut, "OUT", dut.CLK)
        self.slave_stream_out = MISlaveMonitor(dut, "IN", dut.CLK)

        self.backpressure = BitDriver(dut.OUT_ARDY, dut.CLK)

        # Create a scoreboard on the master_stream_out bus
        self.pkts_sent = 0
        self.expected_output_master = []
        self.expected_output_slave = []
        self.scoreboard = Scoreboard(dut)
        self.scoreboard.add_interface(self.master_stream_out, self.expected_output_master)
        self.scoreboard.add_interface(self.slave_stream_out, self.expected_output_slave)

        if debug:
            self.master_stream_in.log.setLevel(cocotb.logging.DEBUG)
            self.master_stream_out.log.setLevel(cocotb.logging.DEBUG)

    def model(self, transaction: bytes, testcase: int):
        """Model the DUT based on the input transaction"""
        if testcase == 0:
            self.expected_output_slave.append(transaction)
        else:
            self.expected_output_master.append(transaction)

        self.pkts_sent += 1

    async def reset(self):
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 2)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)


@cocotb.test()
async def run_test(dut, pkt_count: int = 1000, item_width_min: int = 1, item_width_max: int = 32):
    # Start clock generator
    cocotb.start_soon(Clock(dut.CLK, 5, units='ns').start())
    tb = testbench(dut)
    await tb.reset()

    tb.backpressure.start((1, i % 5) for i in itertools.count())

    for testcase in range(2):
        """two test cases - read = 0, write = 1"""

        item_count = 0

        for transaction in random_packets(item_width_min, item_width_max, pkt_count):
            left_to_enable = len(transaction)

            cycles = (len(transaction) + (tb.master_stream_in.data_width - 1)) // tb.master_stream_in.data_width

            item_count += cycles

            for i in range(cycles):
                if left_to_enable > tb.master_stream_in.data_width:
                    byte_enable = 2**tb.master_stream_in.data_width - 1
                    """setting all bytes of byte enable to 1"""

                    left_to_enable -= tb.master_stream_in.data_width

                else:
                    byte_enable = 2**left_to_enable - 1

                byte_enable = 15 if testcase == 0 else byte_enable

                tb.model((int.from_bytes(transaction[0:tb.master_stream_in.addr_width], 'little') + i * tb.master_stream_in.addr_width, int.from_bytes(transaction[i * tb.master_stream_in.data_width:(i + 1) * tb.master_stream_in.data_width], 'little'), byte_enable), testcase)

            if testcase == 0:
                """read test"""
                cocotb.log.debug(f"generated transaction: {transaction.hex()}")
                tb.master_stream_in.append(("rd", transaction))
                tb.slave_stream_in.append(("rd", transaction))

            else:
                """write test"""
                cocotb.log.debug(f"generated transaction: {transaction.hex()}")
                tb.master_stream_in.append(("wr", transaction))
                tb.slave_stream_in.append(("wr", transaction))

        last_num = 0

        stream_out = tb.slave_stream_out if testcase == 0 else tb.master_stream_out
        transaction_type = "read" if testcase == 0 else "write"

        while stream_out.item_cnt < item_count:
            if stream_out.item_cnt // 1000 > last_num:
                last_num = stream_out.item_cnt // 1000
                cocotb.log.info(f"Number of {transaction_type} transactions processed: {stream_out.item_cnt}/{item_count}")
            await ClockCycles(dut.CLK, 100)

    raise tb.scoreboard.result
