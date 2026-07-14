# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Generated Environment Integration

import random
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotbext.ofm.mvb.drivers import MVBDriver
from cocotbext.ofm.mvb.monitors import MVBMonitor
from cocotbext.ofm.ver.backpressure import BackpressureGenerator, BackpressureConfig
from cocotbext.ofm.ver.generators import random_integers
from cocotb_bus.drivers import BitDriver
from cocotb_bus.scoreboard import Scoreboard
from cocotbext.ofm.utils.throughput_probe import ThroughputProbe, ThroughputProbeMvbInterface
from cocotbext.ofm.base.generators import ItemRateLimiter
from cocotbext.ofm.mvb.transaction import MvbTrClassicWithMeta


class testbench():
    # dut = device tree of the tested component
    def __init__(self, dut, debug=False):
        self.dut = dut

        # setting up the input driver and connecting it to signals beginning with "RX"
        self.stream_in = MVBDriver(dut, "RX_MVB", dut.CLK)

        # setting up the output monitor and connecting it to signals beginning with "TX"
        self.stream_out = MVBMonitor(dut, "TX_MVB", dut.CLK, tr_type=MvbTrClassicWithMeta)

        # setting up driver of the DST_RDY so it randomly fluctuates between 0 and 1
        self.backpressure = BitDriver(dut.TX_MVB_DST_RDY, dut.CLK)

        # setting up the probe measuring throughput
        self.throughput_probe = ThroughputProbe(ThroughputProbeMvbInterface(self.stream_out), throughput_units="items")
        self.throughput_probe.set_log_period(10)
        self.throughput_probe.add_log_interval(0, None)

        # counter of sent transactions
        self.pkts_sent = 0

        # list of the transactions that are expected to be received
        self.expected_output = []

        # setting up a scoreboard which compares received transactions with the expected transactions
        self.scoreboard = Scoreboard(dut)

        # linking a monitor with its expected output
        self.scoreboard.add_interface(self.stream_out, self.expected_output)

        # setting up the logging level
        if debug:
            self.stream_in.log.setLevel(cocotb.logging.DEBUG)
            self.stream_out.log.setLevel(cocotb.logging.DEBUG)

    # method for adding transactions to the expected output
    def model(self, transaction):
        """Model the DUT based on the input transaction"""
        self.expected_output.append(transaction)
        self.pkts_sent += 1

    # method preforming a hardware reset
    async def reset(self):
        self.dut.RST.value = 1
        await ClockCycles(self.dut.CLK, 10)
        self.dut.RST.value = 0
        await RisingEdge(self.dut.CLK)


# defining a test - functions with "@cocotb.test()" decorator will be automatically found and run
@cocotb.test()
async def run_test(dut, pkt_count=10000):
    # start a clock generator
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())

    # initialization of the test bench
    tb = testbench(dut, debug=False)

    # change MVB driver's IdleGenerator to ItemRateLimiter
    # note: the RateLimiter's rate is affected by backpressure (DST_RDY).
    # Even though it takes into account cycles with DST_RDY=0, the desired rate might not be achievable.
    idle_gen_conf = dict(random_idles=True, max_idles=5, zero_idles_chance=50)
    tb.stream_in.set_idle_generator(ItemRateLimiter(rate_percentage=30, **idle_gen_conf))

    # running simulated reset
    await tb.reset()

    # starting the BitDriver (randomized DST_RDY)
    tb.backpressure.start(BackpressureGenerator(BackpressureConfig(1, 5, 0.5)))

    # dynamically getting the width of the data signal that will be set (useful if the width of the signal may change)
    data_width = tb.stream_in.item_widths["data"]
    meta_width = tb.stream_in.item_widths["meta"]

    # generating MVB items as random integers between the minimum and maximum unsigned value of the item
    for transaction in random_integers(0, 2**data_width-1, pkt_count):
        random_mvb_transaction = random.randint(0, 2**meta_width - 1)

        # logging the generated transaction
        cocotb.log.debug(f"generated transaction: {hex(transaction)}")

        # initializing MVB transaction object
        mvb_tr = MvbTrClassicWithMeta()

        # setting data of MVB transaction to the generated integer
        mvb_tr.data = transaction
        mvb_tr.meta = random_mvb_transaction

        # appending the transaction to tb.expected_output
        tb.model(mvb_tr)

        # passing the transaction to the driver which then writes it to the bus
        tb.stream_in.append(mvb_tr)

    last_num = 0

    # checking if all the expected packets have been received
    while (tb.stream_out.item_cnt < pkt_count):

        # logging number of received packets after every 1000 packets
        if (tb.stream_out.item_cnt // 1000) > last_num:
            last_num = tb.stream_out.item_cnt // 1000
            cocotb.log.info(f"Number of transactions processed: {tb.stream_out.item_cnt}/{pkt_count}")

        # if not all packets have been received yet, waiting 100 cycles so the simulation doesn't stop prematurely
        await ClockCycles(dut.CLK, 100)

    # logging values measured by throughput probe
    tb.throughput_probe.log_max_throughput()
    tb.throughput_probe.log_average_throughput()

    # displaying result of the test
    raise tb.scoreboard.result
