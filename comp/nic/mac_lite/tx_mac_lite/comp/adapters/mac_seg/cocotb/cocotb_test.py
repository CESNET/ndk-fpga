# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025-2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotbext.ofm.mfb.drivers import MFBDriver
from cocotbext.ofm.mac_segmented.monitors import MAC_Segmented_TX_Monitor
from cocotbext.ofm.ver.generators import random_packets
from cocotb_bus.drivers import BitDriver
from cocotb_bus.scoreboard import Scoreboard
#from cocotbext.ofm.utils.throughput_probe import ThroughputProbe, ThroughputProbeMfbInterface


class testbench():
    def __init__(self, dut, debug=False):
        self.dut = dut
        self.stream_in = MFBDriver(dut, "IN_MFB", dut.CLK)
        self.backpressure = BitDriver(dut.IN_MFB_DST_RDY, dut.CLK)
        self.stream_out = MAC_Segmented_TX_Monitor(dut, "OUT_MAC", dut.CLK)

        #self.throughput_probe = ThroughputProbe(ThroughputProbeMfbInterface(self.stream_out), throughput_units="bits")
        #self.throughput_probe.add_log_interval(0, None)
        #self.throughput_probe.set_log_period(10)

        # Create a scoreboard on the stream_out bus
        self.pkts_sent = 0
        self.expected_output = []
        self.scoreboard = Scoreboard(dut)
        self.scoreboard.add_interface(self.stream_out, self.expected_output)

        if debug:
            self.stream_in.log.setLevel(cocotb.logging.DEBUG)
            self.stream_out.log.setLevel(cocotb.logging.DEBUG)

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
async def run_test(dut, pkt_count=10000, frame_size_min=60, frame_size_max=2048):
    # Start clock generator
    cocotb.start_soon(Clock(dut.CLK, 2482, units="ps").start())
    tb = testbench(dut, debug=True)
    dut.IN_MFB_ERROR.value = 0
    dut.OUT_MAC_READY.value = 1
    await tb.reset()
    dut.IN_MFB_DST_RDY.value = 1

    for transaction in random_packets(frame_size_min, frame_size_max, pkt_count):
        tb.model(transaction)
        cocotb.log.debug("generated transaction: " + transaction.hex())
        tb.stream_in.append(transaction)

    last_num = 0
    while (tb.stream_out.frame_cnt < pkt_count):
        if (tb.stream_out.frame_cnt // 1000) > last_num:
            last_num = tb.stream_out.frame_cnt // 1000
            cocotb.log.info("Number of transactions processed: %d/%d" % (tb.stream_out.frame_cnt, pkt_count))
        await ClockCycles(dut.CLK, 100)

    await ClockCycles(dut.CLK, 100)
    cocotb.log.debug("RX: %d/%d" % (tb.stream_in.frame_cnt, pkt_count))
    cocotb.log.debug("TX: %d/%d" % (tb.stream_out.frame_cnt, pkt_count))
    cocotb.log.debug("SC: %d/%d" % (tb.pkts_sent, pkt_count))

    #tb.throughput_probe.log_max_throughput()
    #tb.throughput_probe.log_average_throughput()

    raise tb.scoreboard.result
