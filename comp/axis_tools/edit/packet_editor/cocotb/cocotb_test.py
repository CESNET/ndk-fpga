# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): David Vodak <vodak@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Cocotb tests for AXIS_PACKET_EDITOR component."""

import random
from typing import Optional, Tuple

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles
from cocotbext.ofm.base.generators import ItemRateLimiter
from cocotbext.ofm.ver.backpressure import BackpressureConfig, apply_backpressure
from cocotbext.ofm.ver.generators import random_packets

from testbench import EditInstruction, Testbench


def _rand_edit_data(edit_bytes: int) -> bytes:
    """Create random edit data bytes."""
    return bytes(random.getrandbits(8) for _ in range(edit_bytes))


async def _run_test(
    dut,
    pkt_count: int = 1000,
    pkt_range: Tuple[int, int] = (60, 8000),
    tx_cfg: Optional[BackpressureConfig] = None,
    test_name: str = ""
):
    """Run randomized packet editing test."""
    cocotb.log.info(f"Starting AXIS_PACKET_EDITOR {test_name} test")
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())

    tb = Testbench(dut, debug=False)
    await tb.reset()
    cocotb.log.info("Reset completed")

    edit_bytes = tb.edit_bytes
    data_width_bytes = len(dut.RX_AXI_TDATA) // 8

    tb.rx_driver.set_idle_generator(ItemRateLimiter(max_idles=5, zero_idles_chance=50))

    tx_task = None
    if tx_cfg:
        tx_task = cocotb.start_soon(apply_backpressure(dut.TX_AXI_TREADY, dut.CLK, tx_cfg))

    pkt_iter = random_packets(min_size=pkt_range[0], max_size=pkt_range[1], count=pkt_count)

    for i, pkt_data in enumerate(pkt_iter):
        enable = random.randint(0, 1)
        if enable:
            # Also generate out-of-range offsets to verify safe no-overwrite behavior.
            max_offset = len(pkt_data) + data_width_bytes
            offset = random.randint(0, max_offset)
            mask = random.getrandbits(edit_bytes)
        else:
            offset = random.randint(0, max(1, len(pkt_data)))
            mask = random.getrandbits(edit_bytes)

        edit_instr = EditInstruction(
            edit_data=_rand_edit_data(edit_bytes),
            edit_offset=offset,
            edit_mask=mask,
            edit_enable=enable
        )

        await tb.send_packet_with_edit(pkt_data=pkt_data, edit_instr=edit_instr)

        if (i + 1) % 500 == 0:
            cocotb.log.info(f"Sent {i + 1}/{pkt_count} packets")

    timeout = 0
    while tb.tx_monitor.frame_cnt < pkt_count and timeout < 1000000:
        await ClockCycles(dut.CLK, 10)
        timeout += 1

    if tx_task:
        tx_task.cancel()

    cocotb.log.info(f"Test completed: {tb.tx_monitor.frame_cnt}/{pkt_count} packets")

    if tb.tx_monitor.frame_cnt < pkt_count:
        raise AssertionError(f"Only {tb.tx_monitor.frame_cnt}/{pkt_count} packets processed")
    if tb.scoreboard.errors > 0:
        raise AssertionError(f"Test failed with {tb.scoreboard.errors} errors")


@cocotb.test()
async def run_test_random(dut, pkt_count=2000):
    """Random edits with medium backpressure."""
    await _run_test(
        dut,
        pkt_count=pkt_count,
        pkt_range=(60, 8000),
        tx_cfg=BackpressureConfig(1, 5, 0.5),
        test_name="random",
    )


@cocotb.test()
async def run_test_aggressive_backpressure(dut, pkt_count=2000):
    """Random edits with aggressive backpressure."""
    await _run_test(
        dut,
        pkt_count=pkt_count,
        pkt_range=(60, 8000),
        tx_cfg=BackpressureConfig(10, 50, 0.8),
        test_name="aggressive_backpressure",
    )


@cocotb.test()
async def run_test_cross_packet_safety(dut):
    """Verify edit never leaks into following packet."""
    cocotb.log.info("Starting AXIS_PACKET_EDITOR cross_packet_safety test")
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())

    tb = Testbench(dut, debug=False)
    await tb.reset()

    edit_bytes = tb.edit_bytes
    pkt1 = bytes((i % 256) for i in range(96))
    pkt2 = bytes(0xA5 for _ in range(73))

    # Packet 1: enabled edit that intentionally points behind packet end.
    instr1 = EditInstruction(
        edit_data=bytes(0x55 for _ in range(edit_bytes)),
        edit_offset=len(pkt1) - 2,
        edit_mask=(1 << edit_bytes) - 1,
        edit_enable=1,
    )

    # Packet 2: edit explicitly disabled.
    instr2 = EditInstruction(
        edit_data=bytes(0x11 for _ in range(edit_bytes)),
        edit_offset=0,
        edit_mask=(1 << edit_bytes) - 1,
        edit_enable=0,
    )

    await tb.send_packet_with_edit(pkt1, instr1)
    await tb.send_packet_with_edit(pkt2, instr2)

    timeout = 0
    while tb.tx_monitor.frame_cnt < 2 and timeout < 100000:
        await ClockCycles(dut.CLK, 10)
        timeout += 1

    if tb.tx_monitor.frame_cnt < 2:
        raise AssertionError("Cross-packet safety test timeout")
    if tb.scoreboard.errors > 0:
        raise AssertionError(f"Test failed with {tb.scoreboard.errors} errors")
