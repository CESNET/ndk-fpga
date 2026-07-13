# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025-2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

import itertools
from random import randint

import cocotb
import logging
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotbext.ofm.axi4stream.drivers import Axi4StreamMaster
from cocotbext.ofm.axi4stream.monitors import Axi4Stream
from cocotb_bus.scoreboard import Scoreboard
from cocotbext.ofm.axi4stream.transaction import Axi4StreamTransaction, Axi4StreamTransactionWithSelect
from cocotbext.ofm.ver.multibit_driver import MultiBitDriver, Patterns
from cocotbext.ofm.base.generators import ItemRateLimiter
from cocotbext.ofm.ver.generators import random_transactions
from cocotbext.ofm.utils.math import ceildiv


class testbench():
    def __init__(self, dut, debug=False):
        self.dut = dut
        self.stream_in: Axi4StreamMaster  = Axi4StreamMaster(dut, "RX_AXIS", dut.CLK)
        self.stream_out: list[Axi4Stream] = list()
        self.backpressure = MultiBitDriver(dut.TX_AXIS_TREADY, dut.CLK, pattern=Patterns.random)

        if debug:
            self.stream_in.log.setLevel(logging.DEBUG)

        # Create a scoreboard on the stream_out bus
        self.pkts_sent = 0
        self.expected_output = list()
        self.scoreboard = Scoreboard(dut)

        # generating monitor for every stream
        for i in range(self.dut.TX_STREAMS.value):
            monitor = Axi4Stream(dut, "TX_AXIS", dut.CLK, array_idx=i, trans_type=Axi4StreamTransaction)
            self.stream_out.append(monitor)
            self.expected_output.append(list())
            self.scoreboard.add_interface(self.stream_out[i], self.expected_output[i])

            if debug:
                self.monitor.log.setLevel(logging.DEBUG)
                self.stream_out.log.setLevel(logging.DEBUG)

    def model(self, transaction: Axi4StreamTransaction, index: int):
        """Model the DUT based on the input transaction"""
        self.expected_output[index].append(transaction)

    async def reset(self):
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 10)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)


@cocotb.test()
async def run_test(dut, min_size=4, max_size=512, pkt_count=10000):
    # Start clock generator
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())

    tb = testbench(dut, debug=False)

    # adding rate limiter to driver
    idle_gen_conf = dict(random_idles=True, max_idles=5, zero_idles_chance=50)
    tb.stream_in.set_idle_generator(ItemRateLimiter(rate_percentage=30, **idle_gen_conf))

    await tb.reset()

    # starting bit driver
    tb.backpressure.start((1, i % 5) for i in itertools.count())

    tx_streams = tb.dut.TX_STREAMS.value
    data_width = len(tb.stream_in.bus.TKEEP)
    sel_width  = len(tb.stream_in.bus.SEL)

    # generating and sending transactions
    for transaction in random_transactions(Axi4StreamTransaction, tb.stream_in, "TDATA", min_size, max_size, pkt_count):
        selector = randint(0, tx_streams-1)
        word_cnt = ceildiv(data_width, len(transaction.TDATA))
        sel = 0

        # set selector for every word
        for _ in range(word_cnt):
            sel  = (sel << sel_width) + selector

        # create a seperate transaction object with a selector and copy data from the generated transaction
        send_trans = Axi4StreamTransactionWithSelect()
        send_trans.TDATA = transaction.TDATA
        send_trans.TUSER = transaction.TUSER
        send_trans.SEL   = sel

        tb.model(transaction, selector)

        tb.stream_in.append(send_trans)
        tb.pkts_sent += 1

    # waiting for all transactions to be received
    last_num = 0
    processed = 0

    while processed < pkt_count:
        processed = 0

        # sum up all processed packets of every output channel
        for monitor in tb.stream_out:
            processed += monitor.frame_cnt

        if (processed // 1000) > last_num:
            last_num = processed // 1000
            cocotb.log.info("Number of transactions processed: %d/%d" % (processed, pkt_count))
        await ClockCycles(dut.CLK, 100)

    raise tb.scoreboard.result
