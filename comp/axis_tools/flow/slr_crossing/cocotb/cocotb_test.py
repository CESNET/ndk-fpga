# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>

"""Cocotb tests for AXIS_SLR_CROSSING component."""

import itertools

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, RisingEdge
from cocotb_bus.scoreboard import Scoreboard
from cocotbext.ofm.axi4stream.drivers import Axi4StreamMaster
from cocotbext.ofm.axi4stream.monitors import Axi4Stream
from cocotbext.ofm.axi4stream.transaction import Axi4StreamTransaction
from cocotbext.ofm.ver.generators import random_transactions
from cocotbext.ofm.ver.multibit_driver import MultiBitDriver, Patterns


async def _run_test(dut, pattern, min_size=1, max_size=512, pkt_count=2000, rate_limiter_config=None):
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())

    config = rate_limiter_config or dict(rate_percentage=30, random_idles=True, max_idles=5, zero_idles_chance=50)
    stream_in = Axi4StreamMaster(dut, "RX_AXIS", dut.CLK, rate_limiter_config=config)
    stream_out = Axi4Stream(dut, "TX_AXIS", dut.CLK, trans_type=Axi4StreamTransaction)
    expected = []
    scoreboard = Scoreboard(dut)
    scoreboard.add_interface(stream_out, expected)

    dut.TX_AXIS_TREADY.value = 0
    dut.RESET.value = 1
    await ClockCycles(dut.CLK, 10)
    dut.RESET.value = 0
    await RisingEdge(dut.CLK)

    backpressure = MultiBitDriver(dut.TX_AXIS_TREADY, dut.CLK, pattern=pattern)
    backpressure.start((1, i % 5) for i in itertools.count())

    for transaction in random_transactions(Axi4StreamTransaction, stream_in, "TDATA", min_size, max_size, pkt_count):
        expected.append(transaction)
        stream_in.append(transaction)

    for _ in range(pkt_count * 2000):
        if stream_out.frame_cnt >= pkt_count:
            break
        await ClockCycles(dut.CLK, 10)

    assert stream_out.frame_cnt == pkt_count, f"Received {stream_out.frame_cnt}/{pkt_count} packets"
    assert not expected, f"{len(expected)} packets were not compared"
    raise scoreboard.result


@cocotb.test()
async def run_test_random_backpressure(dut):
    """Random packets with random TX_AXIS_TREADY."""
    await _run_test(dut, Patterns.random)
