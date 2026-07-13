# cocotb_test.py:
# Copyright (C) 2025-2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import itertools
from random import randint, random
from math import log2, ceil
from typing import Tuple

import cocotb
import logging
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb_bus.drivers import BitDriver
from cocotb_bus.scoreboard import Scoreboard

from axi4s_frfr_driver import Axi4sFrfrDriver
from axi4s_frfr_transaction import Axi4sFrfrTransaction
from cocotbext.ofm.axi4stream.monitors import Axi4Stream
from cocotbext.ofm.axi4stream.transaction import Axi4StreamTransaction
from cocotbext.ofm.ver.generators import random_packets
from cocotbext.ofm.base.generators import EthernetRateLimiter


class testbench():
    def __init__(self, dut, debug=False):
        self.dut = dut
        self.axi_rx_drv = Axi4sFrfrDriver(dut, "RX", dut.CLK)
        self.axi_tx_drv = BitDriver(dut.TX_AXI_TREADY, dut.CLK)
        self.axi_tx_mon = Axi4Stream(dut, "TX_AXI", dut.CLK, trans_type=Axi4StreamTransaction)

        self.pkts_sent = 0
        self.expected_output = []
        self.scoreboard = Scoreboard(dut)
        self.scoreboard.add_interface(self.axi_tx_mon, self.expected_output)

        if debug:
            self.axi_rx_drv.log.setLevel(logging.DEBUG)
            self.axi_tx_mon.log.setLevel(logging.DEBUG)

    def model(self, tr: Axi4StreamTransaction, word_bytes: int):
        """Model of the DUT"""
        recv_data = tr.TDATA # the full packet
        pkt = b"" # the fractured part of the packet
        fracture_en = tr.FRACTURE_EN.copy()
        fracture_offset = tr.FRACTURE_OFFSET.copy()

        while len(recv_data) > word_bytes:
            en = fracture_en.pop(0) # Remove and use the first element
            off = fracture_offset.pop(0) + 1 # +1 because we want to include the last byte of the "old" pkt
            if en:
                pkt += recv_data[0:off]
                tx_axi_tr = Axi4StreamTransaction()
                tx_axi_tr.TDATA = pkt
                self.expected_output.append(tx_axi_tr)
                self.pkts_sent += 1
                pkt = recv_data[off:word_bytes]
            else:
                pkt += recv_data[0:word_bytes]
            recv_data = recv_data[word_bytes:]

        # Handle last word (last offset will never be further than to the end of the pkt)
        en = fracture_en.pop(0)
        off = fracture_offset.pop(0) + 1
        if en:
            pkt += recv_data[0:off]
            tx_axi_tr = Axi4StreamTransaction()
            tx_axi_tr.TDATA = pkt
            self.expected_output.append(tx_axi_tr)
            self.pkts_sent += 1
            pkt = recv_data[off:]
        else:
            pkt += recv_data[0:]

        tx_axi_tr = Axi4StreamTransaction()
        tx_axi_tr.TDATA = pkt
        self.expected_output.append(tx_axi_tr)
        self.pkts_sent += 1

    async def reset(self):
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 10)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)


def gen_fracture(weight: float, maximum: int) -> Tuple[int, int]:
    if maximum <= 0:
        return 0, 0
    offset = randint(0, maximum)
    enable = 1 if random() < weight else 0
    return enable, offset


@cocotb.test()
async def run_test(dut, frame_count=5000, frame_size_min=60, frame_size_max=1500, fracture_weight=0.3):
    dut.RESET.value = 1
    cocotb.start_soon(Clock(dut.CLK, 5, unit='ns').start())

    tb = testbench(dut)
    rl = EthernetRateLimiter(bitrate=500_000)
    rl.configure(clk_freq=200_000_000, bits_per_word=tb.dut.AXI_TDATA_WIDTH.value)
    tb.axi_rx_drv.set_idle_generator(rl)
    await tb.reset()

    cocotb.log.info("\n--- Beginning the test ---\n")

    tb.axi_tx_drv.start((1, i % 3) for i in itertools.count())
    await ClockCycles(tb.dut.CLK, 10)

    word_w = tb.dut.AXI_TDATA_WIDTH.value // 8 # in bytes
    fracture_off_w = ceil(log2(word_w)) # Offset signal width (in bits)
    for pkt in random_packets(frame_size_min, frame_size_max, frame_count):
        # packet to axi transaction
        axi_tr = Axi4sFrfrTransaction()
        axi_tr.TDATA = pkt
        fractures = []
        pkt_len = len(pkt)
        while pkt_len > word_w:
            fractures.append(gen_fracture(fracture_weight, 2**fracture_off_w-1))
            pkt_len -= word_w
        fractures.append(gen_fracture(fracture_weight, pkt_len-2)) # -2 to avoid offset pointing to the last byte of the word
        enables, offsets = zip(*fractures)
        axi_tr.FRACTURE_EN = list(enables)
        axi_tr.FRACTURE_OFFSET = list(offsets)

        # Send to Driver (DUT)
        tb.axi_rx_drv.append(axi_tr)

        # Send to Model
        tb.model(axi_tr, word_w)

    await ClockCycles(dut.CLK, 1000) # Wait for at least the first packet to reach the DUT's output
    last_num = 0
    while (this_num := tb.axi_tx_mon.frame_cnt) > last_num:
        last_num = this_num
        cocotb.log.info(f"Number of transactions processed: {tb.axi_tx_mon.frame_cnt}")
        await ClockCycles(dut.CLK, 5000)

    cocotb.log.info("\n--- Test complete, getting results ---\n")
    raise tb.scoreboard.result
