# SPDX-License-Identifier: %s
# Copyright (C) %i %s
# Author(s): %s <%s>

import itertools
import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb_bus.scoreboard import Scoreboard
from cocotb_bus.drivers import BitDriver
from cocotb_bus.monitors import BusMonitor
from cocotbext.ofm.base.drivers import BusDriver
from cocotbext.ofm.ver.generators import random_packets
from cocotbext.ofm.base.generators import ItemRateLimiter
from cocotbext.ofm.utils.throughput_probe import ThroughputProbe


# definition of the class encapsulating components of the test
class testbench():
    # dut = device tree of the tested component
    def __init__(self, dut, debug=False):
        self.dut = dut

        # setting up the input driver
        self.stream_in: BusDriver = None

        # setting up the output monitor
        self.stream_out: BusMonitor = None

        # setting up driver of the DST_RDY so it randomly fluctuates between 0 and 1
        self.backpressure: BitDriver = BitDriver(dut.DST_RDY, dut.CLK)

        # setting up the probe measuring throughput
        self.throughput_probe: ThroughputProbe = None
        self.throughput_probe.set_log_period(10)
        self.throughput_probe.add_log_interval(0, None)

        # counter of sent transactions
        self.pkts_sent: int = 0

        # list of the transactions that are expected to be received
        self.expected_output: list = []

        # setting up a scoreboard which compares received transactions with the expected transactions
        self.scoreboard: Scoreboard = Scoreboard(dut)

        # linking a monitor with its expected output
        self.scoreboard.add_interface(self.stream_out, self.expected_output)

        # setting up the logging level
        if debug:
            self.stream_in.log.setLevel(cocotb.logging.DEBUG)
            self.stream_out.log.setLevel(cocotb.logging.DEBUG)

    # method for adding transactions to the expected output
    def model(self, transaction):
        # Model the DUT based on the input transaction
        self.expected_output.append(transaction)
        self.pkts_sent += 1

    # method preforming a hardware reset
    async def reset(self):
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 10)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)


# defining a test - functions with "@cocotb.test()" decorator will be automatically found and run
@cocotb.test()
async def run_test(dut, min_length=1, max_length=512, pkt_count=10000):
    # start a clock generator
    cocotb.start_soon(Clock(dut.CLK, 5, units="ns").start())

    # initialization of the test bench
    tb = testbench(dut, debug=False)

    # change driver's IdleGenerator to ItemRateLimiter
    # note: the RateLimiter's rate is affected by backpressure (DST_RDY).
    # Even though it takes into account cycles with DST_RDY=0, the desired rate might not be achievable.
    idle_gen_conf = dict(random_idles=True, max_idles=5, zero_idles_chance=50)
    tb.stream_in.set_idle_generator(ItemRateLimiter(rate_percentage=30, **idle_gen_conf))

    # running simulated reset
    await tb.reset()

    # starting the BitDriver (randomized DST_RDY)
    tb.backpressure.start((1, i % 5) for i in itertools.count())

    # generating random packets
    for transaction in random_packets(min_length, max_length, pkt_count):
        # appending the transaction to tb.expected_output
        tb.model(transaction)

        # passing the transaction to the driver which then writes it to the bus
        tb.stream_in.append(transaction)

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
