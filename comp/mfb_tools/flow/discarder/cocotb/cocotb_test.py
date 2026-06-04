# cocotb_test.py:
# Copyright (C) 2025 DynaNIC Semiconductors, Ltd.
# Author(s): Jan Privara <privara@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotbext.ofm.mvb.drivers import MVBDriver
from cocotbext.ofm.mvb.monitors import MVBMonitor
from cocotbext.ofm.mfb.drivers import MFBDriver
from cocotbext.ofm.mfb.monitors import MFBMonitor
from cocotbext.ofm.ver.backpressure import BackpressureGenerator, BackpressureConfig
from cocotbext.ofm.ver.generators import random_packets
from cocotbext.ofm.ver.generators import random_integers
from cocotb_bus.drivers import BitDriver
from cocotb_bus.scoreboard import Scoreboard
from cocotbext.ofm.utils.throughput_probe import ThroughputProbe, ThroughputProbeMfbInterface
from cocotbext.ofm.mvb.transaction import MvbTrClassic
from cocotbext.ofm.mfb.transaction import MfbTransaction


# definition of the class encapsulating components of the test
class testbench():
    # dut = device tree to the tested component
    def __init__(self, dut, debug=False):
        self.dut = dut

        # setting MFB params based on generics
        mfb_params = {
            "regions"     : dut.REGIONS.value,
            "region_size" : dut.MFB_REG_SIZE.value,
            "block_size"  : dut.MFB_BLOCK_SIZE.value,
            "item_width"  : dut.MFB_ITEM_WIDTH.value,
            "meta_width"  : 0
        }

        # setting up the MVB input driver and connecting it to signals beginning with "RX_MVB"
        self.mvb_stream_in = MVBDriver(dut, "RX_MVB", dut.CLK)
        # setting up the MFB input driver and connecting it to signals beginning with "RX_MFB"
        self.mfb_stream_in = MFBDriver(dut, "RX_MFB", dut.CLK, mfb_params=mfb_params)

        # choosing the right transaction type
        self.mfb_trans_type = MfbTransaction

        # setting up the MFB output monitor and connecting it to signals begging with "TX_MFB"
        self.mfb_stream_out = MFBMonitor(dut, "TX_MFB", dut.CLK, mfb_params=mfb_params, trans_type=self.mfb_trans_type)
        # setting up the MVB output monitor and connecting it to signals beginning with "TX_MVB"
        self.mvb_stream_out = MVBMonitor(dut, "TX_MVB", dut.CLK, tr_type=MvbTrClassic)

        # setting up driver of the MFB's DST_RDY so it randomly fluctuates between 0 and 1
        self.mfb_backpressure = BitDriver(dut.TX_MFB_DST_RDY, dut.CLK)
        # setting up driver of the MVB's DST_RDY so it randomly fluctuates between 0 and 1
        self.mvb_backpressure = BitDriver(dut.TX_MVB_DST_RDY, dut.CLK)

        # setting up the probe measuring throughput
        self.mfb_throughput_probe = ThroughputProbe(ThroughputProbeMfbInterface(self.mfb_stream_out), throughput_units="bits")
        self.mfb_throughput_probe.add_log_interval(0, None)
        self.mfb_throughput_probe.set_log_period(10)

        # counter of sent transactions
        self.pkts_sent = 0

        # list of the transactions that are expected to be received
        self.mvb_expected_output = []
        self.mfb_expected_output = []

        # setting up scoreboard which compares received transactions with the expected transactions
        self.scoreboard = Scoreboard(dut)
        # linking monitor with it's expected output
        self.scoreboard.add_interface(self.mvb_stream_out, self.mvb_expected_output)
        self.scoreboard.add_interface(self.mfb_stream_out, self.mfb_expected_output)

        # setting up logging level
        if debug:
            self.mvb_stream_in.log.setLevel(cocotb.logging.DEBUG)
            self.mfb_stream_in.log.setLevel(cocotb.logging.DEBUG)
            self.mvb_stream_out.log.setLevel(cocotb.logging.DEBUG)
            self.mfb_stream_out.log.setLevel(cocotb.logging.DEBUG)

    # method for adding transactions to expected output
    def model(self, mvb_transaction, mfb_transaction):
        """Model the DUT based on the input transactions"""
        self.mvb_expected_output.append(mvb_transaction)
        self.mfb_expected_output.append(mfb_transaction)
        self.pkts_sent += 1

    # simulation of reset
    async def reset(self):
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 2)
        self.dut.RESET.value = 0
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
    tb.mvb_backpressure.start(BackpressureGenerator(BackpressureConfig(1, 5, 0.5)))
    tb.mfb_backpressure.start(BackpressureGenerator(BackpressureConfig(1, 5, 0.5)))

    # dynamically getting the width of the data signal that will be set (useful if the width of the signal may change)
    mvb_data_width = tb.mvb_stream_in.item_widths["data"]

    # generate random packets - mfb and mvb transactions
    packets_mvb = random_integers(0, 2**mvb_data_width-1, pkt_count)
    packets_mfb = random_packets(frame_size_min, frame_size_max, pkt_count)
    packets_discard = random_integers(0, 1, pkt_count)
    exp_out_pkts = 0

    # generate transactions from mvb and mfb packet pairs
    for (packet_mvb, packet_mfb, discard) in zip(packets_mvb, packets_mfb, packets_discard):
        # creating new MVB transaction object, assigning data
        mvb_tr = MvbTrClassic()
        mvb_tr.data = packet_mvb
        mvb_tr.discard = discard

        # creating new MFB transaction object, assigning data
        mfb_tr      = tb.mfb_trans_type()
        mfb_tr.data = packet_mfb

        if (discard == 0):
            # adding generated packet to expected output
            tb.model(mvb_tr, mfb_tr)
            exp_out_pkts += 1

        # logging the generated packet
        cocotb.log.debug(f"generated transaction: MVB: {mvb_tr},\n MFB: {mfb_tr}")

        # passing generated packet to the driver to be sent to the bus
        tb.mvb_stream_in.append(mvb_tr)
        tb.mfb_stream_in.append(mfb_tr)

    last_num = 0
    # checking if all the expected packets have been received
    while (tb.mfb_stream_out.frame_cnt < exp_out_pkts):
        # logging number of received packets after every 1000 packets
        if (tb.mfb_stream_out.frame_cnt // 1000) > last_num:
            last_num = tb.mfb_stream_out.frame_cnt // 1000
            cocotb.log.info("Number of transactions processed: %d/%d" % (tb.mfb_stream_out.frame_cnt, exp_out_pkts))
        # if not all packets have been received yet, waiting 100 cycles so the simulation doesn't stop prematurelly
        await ClockCycles(dut.CLK, 100)

    cocotb.log.info("Number of transactions processed: %d/%d" % (tb.mfb_stream_out.frame_cnt, exp_out_pkts))

    # logging values measured by throughput probe
    tb.mfb_throughput_probe.log_max_throughput()
    tb.mfb_throughput_probe.log_average_throughput()

    # displaying result of the test
    raise tb.scoreboard.result
