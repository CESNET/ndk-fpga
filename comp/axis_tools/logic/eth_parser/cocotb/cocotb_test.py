# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Cocotb tests for AXIS_ETH_PARSER component.

Tests:
- run_test_base: Random gaps and moderate backpressure on both axes
- run_test_headers_backpressure: Strong backpressure on HEADERS_READY
"""

from typing import Optional, Tuple

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles
from cocotbext.ofm.base.generators import ItemRateLimiter
from cocotbext.ofm.ver.backpressure import BackpressureConfig, apply_backpressure

from testbench import Testbench


async def _run_test(
    dut,
    pkt_count: int = 3000,
    pkt_range: Tuple[int, int] = (60, 1500),
    tx_cfg: Optional[BackpressureConfig] = None,
    hdr_cfg: Optional[BackpressureConfig] = None,
    corrupt_prob: float = 0.05,
    test_name: str = ""
):
    """Common test runner."""
    cocotb.log.info(f"Starting AXIS_ETH_PARSER {test_name} test")
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())

    tb = Testbench(dut, debug=False)
    await tb.reset()
    cocotb.log.info("Reset completed")

    tb.rx_driver.set_idle_generator(ItemRateLimiter(max_idles=5, zero_idles_chance=50))
    tb.tx_driver.bus.TREADY.value = 1

    tx_task = cocotb.start_soon(apply_backpressure(dut.TX_AXI_TREADY, dut.CLK, tx_cfg))
    hdr_task = cocotb.start_soon(apply_backpressure(dut.HEADERS_READY, dut.CLK, hdr_cfg))

    for i in range(pkt_count):
        await tb.generate_and_send_packet(
            min_len=pkt_range[0], max_len=pkt_range[1], corrupt_prob=corrupt_prob
        )
        if (i + 1) % 500 == 0:
            cocotb.log.info(f"Sent {i + 1}/{pkt_count} packets")

    timeout = 0
    last_item_cnt = 0
    while tb.headers_monitor.item_cnt < pkt_count and timeout < 1000000:
        if tb.headers_monitor.item_cnt % 200 == 0 and tb.headers_monitor.item_cnt != last_item_cnt:
            last_item_cnt = tb.headers_monitor.item_cnt
            cocotb.log.info(f"Headers captured: {tb.headers_monitor.item_cnt}/{pkt_count}")
        await ClockCycles(dut.CLK, 10)
        timeout += 1

    tx_task.kill()
    hdr_task.kill()

    cocotb.log.info(f"Test completed: {tb.headers_monitor.item_cnt}/{pkt_count} packets")

    if tb.headers_monitor.item_cnt < pkt_count:
        raise AssertionError(f"Only {tb.headers_monitor.item_cnt}/{pkt_count} packets processed")
    if tb.scoreboard.errors > 0:
        raise AssertionError(f"Test failed with {tb.scoreboard.errors} errors")


@cocotb.test()
async def run_test_base(dut, pkt_count=3000):
    """Base test: moderate backpressure on TX and HEADERS_READY."""
    await _run_test(
        dut, pkt_count=pkt_count,
        tx_cfg=BackpressureConfig(1, 5, 0.5),
        hdr_cfg=BackpressureConfig(1, 5, 0.5),
        test_name="base"
    )


@cocotb.test()
async def run_test_headers_backpressure(dut, pkt_count=2000):
    """Headers backpressure test: strong HEADERS_READY, light TX backpressure."""
    await _run_test(
        dut, pkt_count=pkt_count,
        tx_cfg=BackpressureConfig(1, 5, 0.1),
        hdr_cfg=BackpressureConfig(20, 200, 0.9),
        test_name="headers_backpressure"
    )


@cocotb.test()
async def run_test_corruption(dut, pkt_count=2000):
    """Corruption test: 50% packet corruption with base backpressure."""
    await _run_test(
        dut, pkt_count=pkt_count,
        tx_cfg=BackpressureConfig(1, 5, 0.5),
        hdr_cfg=BackpressureConfig(1, 5, 0.5),
        corrupt_prob=0.5,
        test_name="corruption"
    )
