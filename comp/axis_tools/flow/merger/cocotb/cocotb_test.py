# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025-2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

import itertools

import cocotb
import logging
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, FallingEdge, ReadOnly, RisingEdge, Timer
from cocotbext.ofm.axi4stream.drivers import Axi4StreamMaster
from cocotbext.ofm.axi4stream.monitors import Axi4Stream
from cocotbext.ofm.axi4stream.transaction import Axi4StreamTransaction
from scoreboard import Scoreboard
from cocotb_bus.drivers import BitDriver
from random import randint
from cocotbext.ofm.ver.generators import random_transactions


class testbench():
    def __init__(self, dut, debug=False):
        self.dut = dut
        self.stream_in: list[Axi4StreamMaster]  = list()
        self.stream_out: Axi4Stream = Axi4Stream(dut, "TX_AXIS", dut.CLK, trans_type=Axi4StreamTransaction)
        self.backpressure = BitDriver(dut.TX_AXIS_TREADY, dut.CLK)

        if debug:
            self.stream_out.log.setLevel(logging.DEBUG)

        # Create a scoreboard on the stream_out bus
        self.pkts_sent = 0
        self.expected_output = []
        self.scoreboard = Scoreboard(dut)
        self.scoreboard.add_interface(self.stream_out, self.expected_output)

        # generating driver for every stream
        rate_limiter_config = dict(rate_percentage=30, random_idles=True, max_idles=5, zero_idles_chance=50)
        for i in range(self.dut.RX_STREAMS.value):
            driver = Axi4StreamMaster(dut, "RX_AXIS", dut.CLK, array_idx=i, rate_limiter_config=rate_limiter_config)
            self.stream_in.append(driver)

            if debug:
                self.driver.log.setLevel(logging.DEBUG)

    def model(self, transaction: Axi4StreamTransaction):
        """Model the DUT based on the input transaction"""
        self.expected_output.append(transaction)

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

    await tb.reset()

    # starting bit driver
    tb.backpressure.start((1, i % 5) for i in itertools.count())

    rx_streams = tb.dut.RX_STREAMS.value

    # generating and sending transactions
    for transaction in random_transactions(Axi4StreamTransaction, tb.stream_in[0], "TDATA", min_size, max_size, pkt_count):
        selector = randint(0, rx_streams-1)

        tb.model(transaction)

        tb.stream_in[selector].append(transaction)
        tb.pkts_sent += 1

    # waiting for all transactions to be received
    last_num = 0

    while (tb.stream_out.frame_cnt < pkt_count):
        if (tb.stream_out.frame_cnt // 1000) > last_num:
            last_num = tb.stream_out.frame_cnt // 1000
            cocotb.log.info("Number of transactions processed: %d/%d" % (tb.stream_out.frame_cnt, pkt_count))
        await ClockCycles(dut.CLK, 100)

    raise tb.scoreboard.result


@cocotb.test()
async def test_tvalid_pulse_between_clock_edges(dut):
    """A pulse of TVALID without a clock edge is not a word and must not stop the other streams."""
    cocotb.start_soon(Clock(dut.CLK, 10, unit="ns").start())
    rx_streams = int(dut.RX_STREAMS.value)
    dut.RX_AXIS_TVALID.value = 0
    dut.RX_AXIS_TLAST.value = 0
    dut.TX_AXIS_TREADY.value = 1
    dut.RESET.value = 1
    await ClockCycles(dut.CLK, 10)
    dut.RESET.value = 0
    await ClockCycles(dut.CLK, 10)

    # Stream 0 is selected. Its TVALID is high with TLAST low only between two clock edges.
    await FallingEdge(dut.CLK)
    dut.RX_AXIS_TVALID.value = 1
    await Timer(1, unit="ns")
    dut.RX_AXIS_TVALID.value = 0
    await ClockCycles(dut.CLK, 10)

    # a packet of the other stream must come out
    other = rx_streams - 1
    dut.RX_AXIS_TVALID.value = 1 << other
    dut.RX_AXIS_TLAST.value = 1 << other
    for _ in range(10):
        await RisingEdge(dut.CLK)
        await ReadOnly()
        if str(dut.RX_AXIS_TREADY.value[other]) == "1":
            return
    assert False, "the stream has no RX_AXIS_TREADY after a pulse of TVALID on another stream"
