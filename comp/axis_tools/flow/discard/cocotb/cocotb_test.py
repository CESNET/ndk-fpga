# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Cocotb tests for AXIS_DISCARD component."""

import random
from dataclasses import dataclass
from typing import Optional, Tuple

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles
from cocotbext.ofm.base.generators import ItemRateLimiter
from cocotbext.ofm.ver.generators import random_packets

from testbench import Testbench, DiscardInstruction


@dataclass
class BPCfg:
    """Backpressure configuration."""
    min_hold: int = 1
    max_hold: int = 5
    low_prob: float = 0.5


async def _backpressure(signal, clock, cfg: Optional[BPCfg] = None):
    """Apply random backpressure to a ready signal."""
    cfg = cfg or BPCfg()
    while True:
        hold_cycles = random.randint(cfg.min_hold, cfg.max_hold)
        if random.random() < cfg.low_prob:
            signal.value = 0
        else:
            signal.value = 1
        await ClockCycles(clock, hold_cycles)


async def _run_test(
    dut,
    pkt_count: int = 10,
    pkt_range: Tuple[int, int] = (60, 8000),
    discard_prob: float = 0.5,
    tx_cfg: Optional[BPCfg] = None,
    test_name: str = "",
    zero_idles_chance: int = 50,
    max_idles: int = 5
):
    """Run test with specified packet count and configuration."""
    cocotb.log.info(f"Starting AXIS_DISCARD {test_name} test")
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())

    tb = Testbench(dut, debug=False)
    await tb.reset()
    cocotb.log.info("Reset completed")

    tb.rx_driver.set_idle_generator(ItemRateLimiter(max_idles=max_idles, zero_idles_chance=zero_idles_chance))

    tx_task = None
    if tx_cfg:
        tx_task = cocotb.start_soon(_backpressure(dut.TX_AXI_TREADY, dut.CLK, tx_cfg))

    pkt_iter = random_packets(min_size=pkt_range[0], max_size=pkt_range[1], count=pkt_count)

    for i, pkt_data in enumerate(pkt_iter):
        discard = 1 if random.random() < discard_prob else 0

        discard_instr = DiscardInstruction(discard=discard)

        await tb.send_packet_with_discard(
            pkt_data=pkt_data,
            discard_instr=discard_instr
        )

        if (i + 1) % 500 == 0:
            cocotb.log.info(f"Sent {i + 1}/{pkt_count} packets")

    # Wait for all expected packets to be processed with timeout
    timeout = 0
    last_frame_cnt = 0
    while tb.tx_monitor.frame_cnt < tb.pkts_expected and timeout < 1000000:
        if tb.tx_monitor.frame_cnt % 200 == 0 and tb.tx_monitor.frame_cnt != last_frame_cnt:
            last_frame_cnt = tb.tx_monitor.frame_cnt
            cocotb.log.info(f"Frames received: {tb.tx_monitor.frame_cnt}/{tb.pkts_expected}")
        await ClockCycles(dut.CLK, 10)
        timeout += 1

    if tx_task:
        tx_task.cancel()

    cocotb.log.info(f"Test completed: {tb.tx_monitor.frame_cnt}/{tb.pkts_expected} packets "
                    f"(total sent: {tb.pkts_sent}, discarded: {tb.pkts_sent - tb.pkts_expected})")

    if tb.tx_monitor.frame_cnt < tb.pkts_expected:
        raise AssertionError(f"Only {tb.tx_monitor.frame_cnt}/{tb.pkts_expected} packets processed")
    if tb.scoreboard.errors > 0:
        raise AssertionError(f"Test failed with {tb.scoreboard.errors} errors")


@cocotb.test()
async def run_test_random(dut, pkt_count=3000):
    """Test with fully random packet lengths and ~50% discard probability."""
    await _run_test(
        dut, pkt_count=pkt_count,
        pkt_range=(60, 8000),
        discard_prob=0.5,
        tx_cfg=BPCfg(1, 5, 0.5),
        test_name="random",
        zero_idles_chance=50,
        max_idles=5
    )


@cocotb.test()
async def run_test_aggressive_backpressure(dut, pkt_count=3000):
    """Test with aggressive backpressure on TX interface."""
    await _run_test(
        dut, pkt_count=pkt_count,
        pkt_range=(60, 8000),
        discard_prob=0.5,
        tx_cfg=BPCfg(10, 50, 0.8),
        test_name="aggressive_backpressure",
        zero_idles_chance=50,
        max_idles=5
    )


@cocotb.test()
async def run_test_high_discard_rate(dut, pkt_count=3000):
    """Test with high discard probability (90%)."""
    await _run_test(
        dut, pkt_count=pkt_count,
        pkt_range=(60, 8000),
        discard_prob=0.9,
        tx_cfg=BPCfg(1, 5, 0.5),
        test_name="high_discard_rate",
        zero_idles_chance=50,
        max_idles=5
    )


@cocotb.test()
async def run_test_low_discard_rate(dut, pkt_count=3000):
    """Test with low discard probability (10%)."""
    await _run_test(
        dut, pkt_count=pkt_count,
        pkt_range=(60, 8000),
        discard_prob=0.1,
        tx_cfg=BPCfg(1, 5, 0.5),
        test_name="low_discard_rate",
        zero_idles_chance=50,
        max_idles=5
    )


@cocotb.test()
async def run_test_no_discard(dut, pkt_count=2000):
    """Test with no discards - all packets should pass through."""
    await _run_test(
        dut, pkt_count=pkt_count,
        pkt_range=(60, 8000),
        discard_prob=0.0,
        tx_cfg=BPCfg(1, 5, 0.5),
        test_name="no_discard",
        zero_idles_chance=50,
        max_idles=5
    )


@cocotb.test()
async def run_test_all_discard(dut, pkt_count=2000):
    """Test with all packets discarded - no packets should appear on TX."""
    await _run_test(
        dut, pkt_count=pkt_count,
        pkt_range=(60, 8000),
        discard_prob=1.0,
        tx_cfg=BPCfg(1, 5, 0.5),
        test_name="all_discard",
        zero_idles_chance=50,
        max_idles=5
    )


@cocotb.test()
async def run_test_small_packets(dut, pkt_count=3000):
    """Test with small packets from 60 to 75 bytes."""
    await _run_test(
        dut, pkt_count=pkt_count,
        pkt_range=(60, 75),
        discard_prob=0.5,
        tx_cfg=BPCfg(1, 10, 0.3),
        test_name="small_packets",
        zero_idles_chance=0,
        max_idles=10
    )


@cocotb.test()
async def run_test_jumbo_packets(dut, pkt_count=1000):
    """Test with jumbo packets up to 9216 bytes."""
    await _run_test(
        dut, pkt_count=pkt_count,
        pkt_range=(4000, 9216),
        discard_prob=0.5,
        tx_cfg=BPCfg(1, 5, 0.5),
        test_name="jumbo_packets",
        zero_idles_chance=50,
        max_idles=5
    )
