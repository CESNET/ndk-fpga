# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Cocotb tests for AXIS_PACKET_EXTENDER component."""

import random
from typing import Optional, Tuple

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles
from cocotbext.ofm.base.generators import IdleGenerator, ItemRateLimiter
from cocotbext.ofm.ver.backpressure import BackpressureConfig, apply_backpressure
from cocotbext.ofm.ver.generators import random_packets

from testbench import Testbench, ExtendInstruction


async def _run_test(
    dut,
    pkt_count: int = 10,
    pkt_range: Tuple[int, int] = (60, 1500),
    tx_cfg: Optional[BackpressureConfig] = None,
    rate_limiter: Optional[IdleGenerator] = IdleGenerator(),
    test_name: str = ""
):
    """Run test with specified packet count and configuration."""
    cocotb.log.debug(f"Starting AXIS_PACKET_EXTENDER {test_name} test")
    clock = Clock(dut.CLK, 5, units="ns")
    cocotb.start_soon(clock.start())

    tb = Testbench(dut, debug=False)
    await tb.reset()
    cocotb.log.info("Reset completed")

    tb.rx_driver.set_idle_generator(rate_limiter)

    tx_task = None
    if tx_cfg:
        tx_task = cocotb.start_soon(apply_backpressure(dut.TX_AXI_TREADY, dut.CLK, tx_cfg))

    pkt_iter = random_packets(min_size=pkt_range[0], max_size=pkt_range[1], count=pkt_count)

    for i, pkt_data in enumerate(pkt_iter):
        # Extension length is random within the supported range.
        ext_len = random.randint(0, tb.max_ext_len)

        ext_instr = ExtendInstruction(ext_len=ext_len)

        await tb.send_packet_with_ext(pkt_data=pkt_data, ext_instr=ext_instr)

        if (i + 1) % 500 == 0:
            cocotb.log.info(f"Sent {i + 1}/{pkt_count} packets")

    # Wait for all packets to be processed with timeout
    timeout = 0
    last_frame_cnt = 0
    while tb.tx_monitor.frame_cnt < pkt_count and timeout < 1000000:
        if tb.tx_monitor.frame_cnt % 200 == 0 and tb.tx_monitor.frame_cnt != last_frame_cnt:
            last_frame_cnt = tb.tx_monitor.frame_cnt
            cocotb.log.info(f"Frames received: {last_frame_cnt}/{pkt_count}")
        await ClockCycles(dut.CLK, 10)
        timeout += 1

    if tx_task:
        tx_task.kill()

    cocotb.log.info(f"Test completed: {tb.tx_monitor.frame_cnt}/{pkt_count} packets")

    if tb.tx_monitor.frame_cnt < pkt_count:
        raise AssertionError(f"Only {tb.tx_monitor.frame_cnt}/{pkt_count} packets processed")
    if tb.scoreboard.errors > 0:
        raise AssertionError(f"Test failed with {tb.scoreboard.errors} errors")


@cocotb.test()
async def run_test_random(dut, pkt_count=10000):
    """Test with fully random packet lengths and extension lengths."""
    await _run_test(
        dut, pkt_count=pkt_count,
        pkt_range=(40, 1500),
        tx_cfg=BackpressureConfig(1, 5, 0.5),
        rate_limiter=ItemRateLimiter(max_idles=5, zero_idles_chance=50),
        test_name="random"
    )


@cocotb.test()
async def run_test_aggressive_backpressure(dut, pkt_count=5000):
    """Test with aggressive backpressure on TX interface."""
    await _run_test(
        dut, pkt_count=pkt_count,
        pkt_range=(40, 500),
        tx_cfg=BackpressureConfig(10, 50, 0.8),
        rate_limiter=ItemRateLimiter(max_idles=5, zero_idles_chance=50),
        test_name="aggressive_backpressure"
    )


@cocotb.test()
async def run_test_full_speed(dut, pkt_count=10000):
    """Test maximum throughput with no idle cycles and no TX backpressure."""
    await _run_test(
        dut, pkt_count=pkt_count,
        pkt_range=(60, 1000),
        tx_cfg=None,
        rate_limiter=IdleGenerator(),
        test_name="full_speed"
    )
