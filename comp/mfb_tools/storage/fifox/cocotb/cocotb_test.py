# cocotb_test.py:
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import itertools

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotbext.ofm.mfb.drivers import MFBDriver
from cocotbext.ofm.mfb.monitors import MFBMonitor
from cocotbext.ofm.ver.generators import random_packets
from cocotb_bus.drivers import BitDriver
from cocotb_bus.scoreboard import Scoreboard
from cocotbext.ofm.utils.throughput_probe import ThroughputProbe, ThroughputProbeMfbInterface

# definition of the class encapsulating components of the test
class testbench():
    # dut = device tree to the tested component
    def __init__(self, dut, debug=False):
        self.dut = dut
        # setting up the input driver and connecting it to signals begging with "RX"
        self.stream_in = MFBDriver(dut, "RX", dut.CLK)
        # setting up the output monitor and connecting it to signals begging with "TX"
        self.stream_out = MFBMonitor(dut, "TX", dut.CLK)
        # setting up driver of the DST_RDY so it randomly fluctuates between 0 and 1
        self.backpressure = BitDriver(dut.TX_DST_RDY, dut.CLK)

        # setting up the probe measuring throughput
        self.throughput_probe = ThroughputProbe(ThroughputProbeMfbInterface(self.stream_out), throughput_units="bits")
        self.throughput_probe.add_log_interval(0, None)
        self.throughput_probe.set_log_period(10)

        # counter of sent transactions
        self.pkts_sent = 0
        # list of the transactions that are expected to be received
        self.expected_output = []
        # setting up scoreboard which compares received transactions with the expected transactions
        self.scoreboard = Scoreboard(dut)
        # linking monitor with it's expected output
        self.scoreboard.add_interface(self.stream_out, self.expected_output)

        # setting up logging level
        if debug:
            self.stream_in.log.setLevel(cocotb.logging.DEBUG)
            self.stream_out.log.setLevel(cocotb.logging.DEBUG)

    # method for adding transactions to expected output
    def model(self, transaction):
        """Model the DUT based on the input transaction"""
        self.expected_output.append(transaction)
        self.pkts_sent += 1

    # simulation of reset
    async def reset(self):
        self.dut.RST.value = 1
        await ClockCycles(self.dut.CLK, 2)
        self.dut.RST.value = 0
        await RisingEdge(self.dut.CLK)


# defining a test. Functions with "@cocotb.test()" decorator will be automatically found and run
@cocotb.test()
async def run_test(dut, pkt_count=10000, frame_size_min=60, frame_size_max=512):
    # Start clock generator
    cocotb.start_soon(Clock(dut.CLK, 5, units="ns").start())

    # initialization of the test bench
    tb = testbench(dut, debug=False)

    # running simulated reset
    await tb.reset()

    # staring the BitDriver (randomized DST_RDY)
    tb.backpressure.start((1, i % 5) for i in itertools.count())

    # generating random packets
    for transaction in random_packets(frame_size_min, frame_size_max, pkt_count):
        # adding generated packet to tb.expected_output
        tb.model(transaction)
        # logging the generated packet
        cocotb.log.debug("generated transaction: " + transaction.hex())
        # passing generated packet to the driver to be sent to the bus
        tb.stream_in.append(transaction)

    last_num = 0
    # checking if all the expected packets have been received
    while (tb.stream_out.frame_cnt < pkt_count):
        # logging number of received packets after every 1000 packets
        if (tb.stream_out.frame_cnt // 1000) > last_num:
            last_num = tb.stream_out.frame_cnt // 1000
            cocotb.log.info("Number of transactions processed: %d/%d" % (tb.stream_out.frame_cnt, pkt_count))
        # if not all packets have been received yet, waiting 100 cycles so the simulation doesn't stop prematurelly
        await ClockCycles(dut.CLK, 100)

    # logging values measured by throughput probe
    tb.throughput_probe.log_max_throughput()
    tb.throughput_probe.log_average_throughput()

    # displaying result of the test
    raise tb.scoreboard.result
