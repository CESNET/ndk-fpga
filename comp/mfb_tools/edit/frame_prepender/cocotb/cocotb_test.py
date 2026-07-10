# cocotb_test.py:
# Copyright (C) 2025-2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import itertools
import sys
from random import randint

import cocotb
import logging
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb_bus.drivers import BitDriver
from cocotb_bus.scoreboard import Scoreboard

from cocotbext.ofm.mfb.drivers import MFBDriver
from cocotbext.ofm.mfb.monitors import MFBMonitor
from cocotbext.ofm.mvb.drivers import MVBDriver, MvbTrClassic
from cocotbext.ofm.base.generators import ItemRateLimiter
from cocotbext.ofm.ver.generators import random_packets


class testbench():
    def __init__(self, dut, debug=False):
        self.dut = dut
        self.mfb_rx_drv = MFBDriver(dut, "RX_MFB", dut.CLK)
        self.mfb_tx_drv = BitDriver(dut.TX_MFB_DST_RDY, dut.CLK)
        self.mvb_rx_drv = MVBDriver(dut, "RX_MVB", dut.CLK)
        self.mfb_tx_mon = MFBMonitor(dut, "TX_MFB", dut.CLK)

        self.pkts_sent = 0
        self.expected_output = []
        self.scoreboard = Scoreboard(dut)
        self.scoreboard.add_interface(self.mfb_tx_mon, self.expected_output)

        if debug:
            self.mfb_rx_drv.log.setLevel(logging.DEBUG)
            self.mvb_rx_drv.log.setLevel(logging.DEBUG)
            self.mfb_tx_mon.log.setLevel(logging.DEBUG)

    def model(self, prepend_tr: bytes, packet_tr: bytes):
        """Model of the DUT"""
        prepended_tr = prepend_tr + packet_tr
        self.expected_output.append(prepended_tr)
        self.pkts_sent += 1

    async def reset(self):
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 10)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)


@cocotb.test()
async def run_test(dut, pkt_count=10000, frame_size_min=60, frame_size_max=1500):
    dut.RESET.value = 1
    cocotb.start_soon(Clock(dut.CLK, 5, unit='ns').start())

    tb = testbench(dut)
    # Change MVB driver's IdleGenerator to ItemRateLimiter
    idle_gen_conf = dict(random_idles=True, max_idles=5, zero_idles_chance=50)
    tb.mvb_rx_drv.set_idle_generator(ItemRateLimiter(rate_percentage=30, **idle_gen_conf))
    # Change MFB driver's IdleGenerator to ItemRateLimiter
    tb.mfb_rx_drv.set_idle_generator(ItemRateLimiter(rate_percentage=30, **idle_gen_conf))
    await tb.reset()

    cocotb.log.info("\n--- Beginning the test ---\n")

    tb.mfb_tx_drv.start((1, i % 3) for i in itertools.count())
    # Option to change MVB drivers Rate Limiter (0 = random Idles = inconsistent rate)
    tb.mvb_rx_drv.set_idle_generator(ItemRateLimiter(rate_percentage=0))
    tb.mfb_rx_drv.set_idle_generator(ItemRateLimiter(rate_percentage=0))

    await ClockCycles(tb.dut.CLK, 10)

    item_bytes = tb.mfb_rx_drv._item_bytes
    for mfb_pkt in random_packets(frame_size_min, frame_size_max, pkt_count, alignment=item_bytes):
        tb.mfb_rx_drv.append(mfb_pkt)

        mvb_tr = MvbTrClassic()
        mvb_bus_width = tb.mvb_rx_drv.item_widths['data']
        mvb_prepend = randint(0, 2**mvb_bus_width-1)
        mvb_tr.data = mvb_prepend
        tb.mvb_rx_drv.append(mvb_tr)

        tb.model(prepend_tr=(mvb_prepend.to_bytes(mvb_bus_width//8, sys.byteorder)), packet_tr=(mfb_pkt))

    last_num = 0
    while (tb.mfb_tx_mon.frame_cnt < pkt_count):
        if (this_num := tb.mfb_tx_mon.frame_cnt // (pkt_count // 10)) > last_num:
            last_num = this_num
            cocotb.log.info(f"Number of transactions processed: {tb.mfb_tx_mon.frame_cnt}/{pkt_count}")
        await ClockCycles(dut.CLK, 100)

    cocotb.log.info("\n--- Test complete, getting results ---\n")
    raise tb.scoreboard.result
