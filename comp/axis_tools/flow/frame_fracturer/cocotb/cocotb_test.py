# cocotb_test.py:
# Copyright (C) 2025-2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import itertools
import os
from random import randint, random
from math import log2, ceil
from typing import List, Tuple

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

    def model(self, tr: Axi4sFrfrTransaction, word_bytes: int):
        """Model of the DUT.

        Processes up to MAX_FRACTURES fracture points per word.
        """
        recv_data = tr.TDATA  # the full packet
        pkt = b""  # the fractured part of the packet
        fracture_en = [list(e) for e in tr.FRACTURE_EN]
        fracture_offset = [list(o) for o in tr.FRACTURE_OFFSET]

        while len(recv_data) > word_bytes:
            en_list = fracture_en.pop(0)
            off_list = fracture_offset.pop(0)
            word_data = recv_data[:word_bytes]
            consumed = 0

            for en, off in zip(en_list, off_list):
                if en:
                    cut = off + 1  # offset is inclusive
                    pkt += word_data[consumed:cut]
                    tx_axi_tr = Axi4StreamTransaction()
                    tx_axi_tr.TDATA = pkt
                    self.expected_output.append(tx_axi_tr)
                    self.pkts_sent += 1
                    pkt = b""
                    consumed = cut

            # Remaining bytes in this word go to the next sub-packet.
            pkt += word_data[consumed:word_bytes]
            recv_data = recv_data[word_bytes:]

        # Handle last word.
        en_list = fracture_en.pop(0)
        off_list = fracture_offset.pop(0)
        word_data = recv_data
        consumed = 0

        for en, off in zip(en_list, off_list):
            if en:
                cut = off + 1
                pkt += word_data[consumed:cut]
                tx_axi_tr = Axi4StreamTransaction()
                tx_axi_tr.TDATA = pkt
                self.expected_output.append(tx_axi_tr)
                self.pkts_sent += 1
                pkt = b""
                consumed = cut

        pkt += word_data[consumed:]
        tx_axi_tr = Axi4StreamTransaction()
        tx_axi_tr.TDATA = pkt
        self.expected_output.append(tx_axi_tr)
        self.pkts_sent += 1

    async def reset(self):
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 10)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)


def gen_fractures(
    max_fractures: int,
    weight: float,
    maximum: int,
) -> Tuple[List[int], List[int]]:
    """Generate up to max_fractures fracture points for one word.

    Returns (enables, offsets) — lists of length max_fractures.
    Offsets are strictly increasing when both slots are enabled.
    """
    enables = [0] * max_fractures
    offsets = [0] * max_fractures

    if maximum <= 0:
        return enables, offsets

    prev_off = -1
    for f in range(max_fractures):
        if random() >= weight:
            break  # no more fractures (contiguous from index 0)
        lo = prev_off + 1
        if f < max_fractures - 1:
            # Leave room for at least one more fracture slot.
            hi = maximum - (max_fractures - 1 - f)
        else:
            hi = maximum
        if lo > hi:
            break
        offsets[f] = randint(lo, hi)
        enables[f] = 1
        prev_off = offsets[f]

    return enables, offsets


@cocotb.test()
async def run_test(dut, frame_count=None, frame_size_min=60, frame_size_max=1500, fracture_weight=0.3):
    # Allow the multi-ver runner to override frame_count via __cocotb_params__.
    if frame_count is None:
        frame_count = int(os.environ.get("COCOTB_FRAME_COUNT", "3000"))

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

    word_w = tb.dut.AXI_TDATA_WIDTH.value // 8  # in bytes
    max_fr = tb.dut.MAX_FRACTURES.value
    fracture_off_w = ceil(log2(word_w))  # Offset signal width (in bits)
    off_max = 2**fracture_off_w - 1

    for pkt in random_packets(frame_size_min, frame_size_max, frame_count):
        # Packet to AXI transaction
        axi_tr = Axi4sFrfrTransaction()
        axi_tr.TDATA = pkt

        en_per_word = []
        off_per_word = []
        pkt_len = len(pkt)

        while pkt_len > word_w:
            en, off = gen_fractures(max_fr, fracture_weight, off_max)
            en_per_word.append(en)
            off_per_word.append(off)
            pkt_len -= word_w

        # Last word: offset must not point past the last valid byte.
        en, off = gen_fractures(max_fr, fracture_weight, pkt_len - 2)
        en_per_word.append(en)
        off_per_word.append(off)

        axi_tr.FRACTURE_EN = en_per_word
        axi_tr.FRACTURE_OFFSET = off_per_word

        # Send to Driver (DUT)
        tb.axi_rx_drv.append(axi_tr)
        # Send to Model
        tb.model(axi_tr, word_w)

    await ClockCycles(dut.CLK, 1000)  # Wait for at least the first packet to reach the DUT's output
    last_num = 0
    while (this_num := tb.axi_tx_mon.frame_cnt) > last_num:
        last_num = this_num
        cocotb.log.info(f"Number of transactions processed: {tb.axi_tx_mon.frame_cnt}")
        await ClockCycles(dut.CLK, 5000)

    cocotb.log.info("\n--- Test complete, getting results ---\n")
    raise tb.scoreboard.result
