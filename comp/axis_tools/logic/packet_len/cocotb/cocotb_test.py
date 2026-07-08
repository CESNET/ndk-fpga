# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): David Vodak <vodak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Cocotb tests for AXIS_PACKET_LEN component.

Tests:
- run_test_random: Random packet lengths with moderate backpressure
- run_test_aggressive_backpressure: Strong backpressure on TX interface
- run_test_jumbo_packets: Jumbo packets up to PKT_MTU (9216 bytes)
- run_test_small_packets: Small packets (1-64 bytes)
- run_test_single_word_packets: Packets that fit in a single AXI word
"""

from typing import Optional, Tuple

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles
from cocotbext.ofm.base.generators import ItemRateLimiter
from cocotbext.ofm.ver.backpressure import BackpressureConfig, apply_backpressure
from cocotbext.ofm.ver.generators import random_packets

from testbench import Testbench


async def _run_test(
    dut,
    pkt_count: int = 10,
    pkt_range: Tuple[int, int] = (60, 8000),
    tx_cfg: Optional[BackpressureConfig] = None,
    test_name: str = "",
    zero_idles_chance: int = 50,
    max_idles: int = 5
):
    """Run test with specified packet count and configuration.

    Sends random packets through the DUT and verifies both:
    1. Data passthrough correctness (via scoreboard).
    2. TX_PACKET_LEN accuracy (via length monitor).

    Args:
        dut: Device Under Test handle.
        pkt_count: Number of packets to send.
        pkt_range: Tuple of (min_size, max_size) in bytes.
        tx_cfg: Backpressure configuration for TX interface (None = no backpressure).
        test_name: Name of the test for logging.
        zero_idles_chance: Probability of zero idle cycles between words.
        max_idles: Maximum number of idle cycles between words.
    """
    cocotb.log.info(f"Starting AXIS_PACKET_LEN {test_name} test")
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())

    tb = Testbench(dut, debug=False)
    await tb.reset()
    cocotb.log.info("Reset completed")

    tb.rx_driver.set_idle_generator(
        ItemRateLimiter(max_idles=max_idles, zero_idles_chance=zero_idles_chance)
    )

    tx_task = None
    if tx_cfg:
        tx_task = cocotb.start_soon(
            apply_backpressure(dut.TX_AXI_TREADY, dut.CLK, tx_cfg)
        )

    pkt_iter = random_packets(min_size=pkt_range[0], max_size=pkt_range[1], count=pkt_count)

    for i, pkt_data in enumerate(pkt_iter):
        await tb.send_packet(pkt_data)

        if (i + 1) % 500 == 0:
            cocotb.log.info(f"Sent {i + 1}/{pkt_count} packets")

    # Wait for all packets to be processed with timeout
    timeout = 0
    last_frame_cnt = 0
    while tb.tx_monitor.frame_cnt < pkt_count and timeout < 1000000:
        if tb.tx_monitor.frame_cnt % 200 == 0 and tb.tx_monitor.frame_cnt != last_frame_cnt:
            last_frame_cnt = tb.tx_monitor.frame_cnt
            cocotb.log.info(f"Frames received: {tb.tx_monitor.frame_cnt}/{pkt_count}")
        await ClockCycles(dut.CLK, 10)
        timeout += 1

    if tx_task:
        tx_task.cancel()

    cocotb.log.info(f"Test completed: {tb.tx_monitor.frame_cnt}/{pkt_count} packets")

    if tb.tx_monitor.frame_cnt < pkt_count:
        raise AssertionError(
            f"Only {tb.tx_monitor.frame_cnt}/{pkt_count} packets processed"
        )
    if tb.scoreboard.errors > 0:
        raise AssertionError(
            f"Data passthrough test failed with {tb.scoreboard.errors} errors"
        )
    if tb.length_errors > 0:
        raise AssertionError(
            f"Packet length test failed with {tb.length_errors} errors"
        )


@cocotb.test()
async def run_test_random(dut, pkt_count=3000):
    """Test with fully random packet lengths and moderate backpressure."""
    await _run_test(
        dut, pkt_count=pkt_count,
        pkt_range=(60, 8000),
        tx_cfg=BackpressureConfig(1, 5, 0.5),
        test_name="random",
        zero_idles_chance=50,
        max_idles=5
    )


@cocotb.test()
async def run_test_aggressive_backpressure(dut, pkt_count=2000):
    """Test with aggressive backpressure on TX interface."""
    await _run_test(
        dut, pkt_count=pkt_count,
        pkt_range=(60, 1500),
        tx_cfg=BackpressureConfig(10, 30, 0.8),
        test_name="aggressive_backpressure",
        zero_idles_chance=50,
        max_idles=5
    )


@cocotb.test()
async def run_test_jumbo_packets(dut, pkt_count=1000):
    """Test with jumbo packets up to PKT_MTU (9216 bytes)."""
    await _run_test(
        dut, pkt_count=pkt_count,
        pkt_range=(4000, 9216),
        tx_cfg=BackpressureConfig(1, 5, 0.5),
        test_name="jumbo_packets",
        zero_idles_chance=50,
        max_idles=5
    )


@cocotb.test()
async def run_test_small_packets(dut, pkt_count=3000):
    """Test with small packets from 1 to 64 bytes."""
    await _run_test(
        dut, pkt_count=pkt_count,
        pkt_range=(1, 64),
        tx_cfg=BackpressureConfig(1, 5, 0.5),
        test_name="small_packets",
        zero_idles_chance=50,
        max_idles=5
    )


@cocotb.test()
async def run_test_no_backpressure(dut, pkt_count=2000):
    """Test with no backpressure - TX always ready."""
    await _run_test(
        dut, pkt_count=pkt_count,
        pkt_range=(60, 8000),
        tx_cfg=None,
        test_name="no_backpressure",
        zero_idles_chance=0,
        max_idles=0
    )
