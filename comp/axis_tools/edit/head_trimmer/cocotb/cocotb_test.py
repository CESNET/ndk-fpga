# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Cocotb tests for AXIS_HEAD_TRIMMER component."""

import random
from dataclasses import dataclass
from typing import Optional, Tuple

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles
from cocotbext.ofm.base.generators import ItemRateLimiter
from cocotbext.ofm.ver.generators import random_packets

from testbench import Testbench, TrimInstruction


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
    tx_cfg: Optional[BPCfg] = None,
    test_name: str = ""
):
    """Run test with specified packet count and configuration."""
    cocotb.log.info(f"Starting AXIS_HEAD_TRIMMER {test_name} test")
    cocotb.start_soon(Clock(dut.CLK, 5, units="ns").start())

    tb = Testbench(dut, debug=False)
    await tb.reset()
    cocotb.log.info("Reset completed")

    tb.rx_driver.set_idle_generator(ItemRateLimiter(max_idles=5, zero_idles_chance=50))

    tx_task = None
    if tx_cfg:
        tx_task = cocotb.start_soon(_backpressure(dut.TX_AXI_TREADY, dut.CLK, tx_cfg))

    pkt_iter = random_packets(min_size=pkt_range[0], max_size=pkt_range[1], count=pkt_count)

    for i, pkt_data in enumerate(pkt_iter):
        trim_enable = random.randint(0, 1)

        # For head trimmer: when trim is enabled, generate trim_length in range 1 to pkt_len-1
        # When trim is disabled, random values are allowed
        pkt_len = len(pkt_data)
        if trim_enable and pkt_len >= 2:
            trim_length = random.randint(1, pkt_len - 1)
        else:
            trim_length = random.randint(0, tb.pkt_mtu)

        trim_instr = TrimInstruction(
            trim_length=trim_length,
            trim_enable=trim_enable
        )

        await tb.send_packet_with_trim(
            pkt_data=pkt_data,
            trim_instr=trim_instr
        )

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
        tx_task.kill()

    cocotb.log.info(f"Test completed: {tb.tx_monitor.frame_cnt}/{pkt_count} packets")

    if tb.tx_monitor.frame_cnt < pkt_count:
        raise AssertionError(f"Only {tb.tx_monitor.frame_cnt}/{pkt_count} packets processed")
    if tb.scoreboard.errors > 0:
        raise AssertionError(f"Test failed with {tb.scoreboard.errors} errors")


@cocotb.test()
async def run_test_random(dut, pkt_count=2000):
    """Test with fully random packet lengths and trim configurations."""
    await _run_test(
        dut, pkt_count=pkt_count,
        pkt_range=(60, 8000),
        tx_cfg=BPCfg(1, 5, 0.5),
        test_name="random"
    )


@cocotb.test()
async def run_test_aggressive_backpressure(dut, pkt_count=2000):
    """Test with aggressive backpressure on TX interface."""
    await _run_test(
        dut, pkt_count=pkt_count,
        pkt_range=(60, 8000),
        tx_cfg=BPCfg(10, 50, 0.8),
        test_name="aggressive_backpressure"
    )


@cocotb.test()
async def run_test_jumbo_packets(dut, pkt_count=2000):
    """Test with jumbo packets up to PKT_MTU (9216 bytes)."""
    await _run_test(
        dut, pkt_count=pkt_count,
        pkt_range=(4000, 9216),
        tx_cfg=BPCfg(1, 5, 0.5),
        test_name="jumbo_packets"
    )
