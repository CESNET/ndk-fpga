# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <ondrejschwarz@cesnet.cz>
#            Daniel Kondys <kondys@cesnet.cz>


import itertools

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotbext.ofm.mvb.drivers import MVBDriver
from cocotbext.ofm.mvb.monitors import MVBMonitor
from cocotbext.ofm.ver.generators import random_integers
from cocotb_bus.drivers import BitDriver
from cocotb_bus.scoreboard import Scoreboard
from cocotbext.ofm.utils.throughput_probe import ThroughputProbe, ThroughputProbeMvbInterface
from cocotbext.ofm.base.generators import ItemRateLimiter
from cocotbext.ofm.mvb.transaction import MvbTrClassic


class testbench():
    def __init__(self, dut, debug=False):
        self.dut = dut
        self.stream_in = MVBDriver(dut, "RX", dut.CLK)
        self.backpressure = BitDriver(dut.TX_DST_RDY, dut.CLK)
        self.stream_out = MVBMonitor(dut, "TX", dut.CLK, tr_type=MvbTrClassic)

        self.throughput_probe = ThroughputProbe(ThroughputProbeMvbInterface(self.stream_out), throughput_units="items")
        self.throughput_probe.set_log_period(10)
        self.throughput_probe.add_log_interval(0, None)

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
        await ClockCycles(self.dut.CLK, 10)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)


@cocotb.test()
async def run_test(dut, pkt_count=10000):
    # Start clock generator
    cocotb.start_soon(Clock(dut.CLK, 5, units="ns").start())
    tb = testbench(dut, debug=False)
    # Change MVB drivers IdleGenerator to ItemRateLimiter
    # Note: the RateLimiter's rate is affected by backpressure (DST_RDY).
    # Eventhough it takes into account cycles with DST_RDY=0, the desired rate might not be achievable.
    idle_gen_conf = dict(random_idles=True, max_idles=5, zero_idles_chance=50)
    tb.stream_in.set_idle_generator(ItemRateLimiter(rate_percentage=30, **idle_gen_conf))
    await tb.reset()
    tb.backpressure.start((1, i % 5) for i in itertools.count())

    data_width = tb.stream_in.item_widths["data"]
    for transaction in random_integers(0, 2**data_width-1, pkt_count):
        cocotb.log.debug(f"generated transaction: {hex(transaction)}")
        mvb_tr = MvbTrClassic()
        mvb_tr.data = transaction
        tb.model(mvb_tr)
        tb.stream_in.append(mvb_tr)

    last_num = 0

    while (tb.stream_out.item_cnt < pkt_count):
        if (tb.stream_out.item_cnt // 1000) > last_num:
            last_num = tb.stream_out.item_cnt // 1000
            cocotb.log.info(f"Number of transactions processed: {tb.stream_out.item_cnt}/{pkt_count}")
        await ClockCycles(dut.CLK, 100)

    tb.throughput_probe.log_max_throughput()
    tb.throughput_probe.log_average_throughput()

    raise tb.scoreboard.result
