# cocotb_test.py:
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotbext.ofm.mfb.drivers import MFBDriver
from cocotbext.ofm.mfb.monitors import MFBMonitor
from cocotbext.ofm.ver.backpressure import BackpressureGenerator, BackpressureConfig
from cocotbext.ofm.ver.generators import random_packets
from cocotb_bus.drivers import BitDriver
from cocotb_bus.scoreboard import Scoreboard
from cocotbext.ofm.utils.throughput_probe import ThroughputProbe, ThroughputProbeMfbInterface
from cocotbext.ofm.mfb.transaction import MfbTransaction, MfbTransactionWithMeta
from cocotbext.ofm.base.generators import ItemRateLimiter
from random import randint


# definition of the class encapsulating components of the test
class testbench():
    # dut = device tree to the tested component
    def __init__(self, dut, debug=False):
        self.dut = dut

        # setting MFB params based on generics
        mfb_params = {
            "regions"     : dut.REGIONS.value,
            "region_size" : dut.REGION_SIZE.value,
            "block_size"  : dut.BLOCK_SIZE.value,
            "item_width"  : dut.ITEM_WIDTH.value,
            "meta_width"  : dut.META_WIDTH.value
        }

        # setting up the input driver and connecting it to signals begging with "RX"
        self.stream_in = MFBDriver(dut, "RX", dut.CLK, mfb_params=mfb_params)
        # adding idle generator to driver
        self.stream_in.set_idle_generator(ItemRateLimiter(max_idles=5, zero_idles_chance=70))
        # choosing the right transaction type based on legth of the meta signal
        self.trans_type = MfbTransactionWithMeta if len(self.stream_in.bus.meta) > 0 else MfbTransaction

        # setting up the output monitor and connecting it to signals begging with "TX"
        self.stream_out = MFBMonitor(dut, "TX", dut.CLK, mfb_params=mfb_params, trans_type=self.trans_type)
        # setting up driver of the DST_RDY so it randomly fluctuates between 0 and 1
        self.backpressure = BitDriver(dut.TX_DST_RDY, dut.CLK)

        # setting up the probes measuring throughput
        self.in_throughput_probe = ThroughputProbe(ThroughputProbeMfbInterface(self.stream_in), throughput_units="bits", name="ThroughputProbe - IN")
        self.in_throughput_probe.add_log_interval(0, None)
        self.in_throughput_probe.set_log_period(10)

        self.out_throughput_probe = ThroughputProbe(ThroughputProbeMfbInterface(self.stream_out), throughput_units="bits", name="ThroughputProbe - OUT")
        self.out_throughput_probe.add_log_interval(0, None)
        self.out_throughput_probe.set_log_period(10)

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

    # staring the BitDriver (randomized DST_RDY)
    tb.backpressure.start(BackpressureGenerator(BackpressureConfig(1, 5, 0.5)))

    # calculating width of the meta signal for a region
    meta_width = len(tb.stream_in.bus.meta) // len(tb.stream_in.bus.sof)

    # calculating number of bytes in an item
    item_bytes = tb.dut.ITEM_WIDTH.value // 8

    # generating random packets
    for packet in random_packets(frame_size_min, frame_size_max, pkt_count, alignment=item_bytes):
        # creating a transaction object and adding data to it
        transaction      = tb.trans_type()
        transaction.data = packet

        # setting meta signal if it's present
        if hasattr(transaction, "meta"):
            transaction.meta = randint(0, 2**meta_width-1)

        # adding generated packet to tb.expected_output
        tb.model(transaction)
        # logging the generated packet
        cocotb.log.debug(f"generated transaction: {transaction}")
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

    # logging values measured by throughput probes
    tb.in_throughput_probe.log_max_throughput()
    tb.in_throughput_probe.log_average_throughput()

    tb.out_throughput_probe.log_max_throughput()
    tb.out_throughput_probe.log_average_throughput()

    # displaying result of the test
    raise tb.scoreboard.result
