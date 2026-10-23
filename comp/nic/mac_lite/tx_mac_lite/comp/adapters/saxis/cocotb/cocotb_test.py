# cocotb_test.py: Cocotb tests of TX_MAC_LITE_ADAPTER_SAXIS
# Copyright (C) 2026 DynaNIC Semiconductors, Ltd.
# Author(s): Vlastimil Kosar <kosar@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Verification of TX_MAC_LITE_ADAPTER_SAXIS (MFB 1,8,8,8 -> DCMAC Segmented AXI-Stream, 4 segments).

The input is driven by MFBDriver of cocotbext-ofm. The main test is one
randomized test run in several scenarios of input idles and output
backpressure. The remaining tests cover all frame lengths and alignments, the
throughput, the reset and the AXI4-Stream VALID/READY rule.

MFBDriver never starts a frame in a word where another frame has ended (one
region) and never deasserts SRC_RDY inside a frame. Frames sharing an input
word, and therefore frames starting in segments 1-3 of the output, are not
generated.
"""

import os
import random
from typing import Any, Optional

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, RisingEdge
from cocotbext.ofm.ver.backpressure import BackpressureConfig, apply_backpressure

from testbench import MfbIdles, Testbench

# 200G DCMAC core clock 390.625 MHz
CLK_PERIOD_PS = 2560
SEGMENTS = 4
SEGMENT_BYTES = 16
MIN_FRAME = 60
FRAMES = int(os.environ.get("COCOTB_TRANSACTIONS", "3000"))

# (input gaps, READY backpressure, frames up to 9600 B)
SCENARIOS = {
    "full_speed":   (None, None, False),
    "block_gaps":   (MfbIdles(60, 63), None, False),
    "word_gaps":    (MfbIdles(50, 192), None, False),
    "backpressure": (MfbIdles(40, 63), BackpressureConfig(1, 6, 0.4), False),
    "everything":   (MfbIdles(40, 192), BackpressureConfig(1, 10, 0.5), True),
}


def frame_sizes(rng: random.Random, count: int, jumbo: bool) -> list[int]:
    sizes = []
    for _ in range(count):
        if jumbo and rng.random() < 0.1:
            sizes.append(rng.randint(1519, 9600))
        elif rng.random() < 0.3:
            sizes.append(rng.randint(MIN_FRAME, MIN_FRAME + 2 * SEGMENTS * SEGMENT_BYTES))
        else:
            sizes.append(rng.randint(MIN_FRAME, 1518))
    return sizes


async def start(dut: Any, seed: int, idles: Optional[MfbIdles] = None) -> Testbench:
    cocotb.start_soon(Clock(dut.CLK, CLK_PERIOD_PS, unit="ps").start())
    random.seed(seed + 1000)
    tb = Testbench(dut, idles)
    await tb.reset()
    return tb


@cocotb.test()
@cocotb.parametrize(scenario=list(SCENARIOS))
async def test_random(dut: Any, scenario: str) -> None:
    """Random frames from 60 B, input idles and READY backpressure; checks data, order and PG369 rules."""
    idles, backpressure, jumbo = SCENARIOS[scenario]
    seed = list(SCENARIOS).index(scenario) + 1
    rng = random.Random(seed)
    tb = await start(dut, seed, idles)
    if backpressure is not None:
        cocotb.start_soon(apply_backpressure(dut.OUT_SAXIS_READY, dut.CLK, backpressure))

    count = FRAMES // 3 if jumbo else FRAMES
    for size in frame_sizes(rng, count, jumbo):
        tb.send(bytes(rng.getrandbits(8) for _ in range(size)))

    await tb.wait_for_frames(count, 400 * count)
    tb.check(count)

    stats = tb.checker.stats
    assert len(stats.mty) == 16, f"MTY values not covered: {sorted(set(range(16)) - set(stats.mty))}"
    assert set(stats.eop_pos) == set(range(SEGMENTS)), "EOP not covered in every segment"
    assert len(tb.in_cov.eof_pos) == 64, "IN_MFB EOF not covered in every byte"
    if idles is not None:
        assert set(tb.in_cov.sof_pos) == set(range(8)), "IN_MFB SOF not covered in every block"
    if backpressure is not None:
        assert stats.stalls_in_frame > 0, "READY never deasserted inside a frame"


@cocotb.test()
async def test_frame_lengths(dut: Any) -> None:
    """Every length from 60 B to 60 B + 3 words, 16 frames each, 90 % of them after an idle gap of 1-63 B."""
    tb = await start(dut, 10, MfbIdles(90, 63))
    rng = random.Random(10)
    count = 0
    for size in range(MIN_FRAME, MIN_FRAME + 3 * 64 + 1):
        for _ in range(16):
            tb.send(bytes(rng.getrandbits(8) for _ in range(size)))
            count += 1
    await tb.wait_for_frames(count, 100 * count)
    tb.check(count)
    assert set(tb.in_cov.sof_pos) == set(range(8)) and len(tb.in_cov.eof_pos) == 64


@cocotb.test()
@cocotb.parametrize(size=[60, 64, 65, 80, 81, 128, 129, 256, 1518, 9600])
async def test_throughput(dut: Any, size: int) -> None:
    """Back-to-back frames with READY = 1: continuous output, the packing efficiency is reported.

    PG369 lets a frame start in the segment after the previous EOP, so the
    minimum is ceil(size / 16) segments per frame packed into 4-segment cycles.
    MFBDriver starts every frame in a new word, so the input limits most
    lengths; the output cycles against both limits are logged.
    """
    tb = await start(dut, size)
    rng = random.Random(size)
    count = max(20, 60000 // size)
    for _ in range(count):
        tb.send(bytes(rng.getrandbits(8) for _ in range(size)))
    await tb.wait_for_frames(count, 100 * count + 1000)
    tb.check(count)

    stats = tb.checker.stats
    segments = -(-size // SEGMENT_BYTES)
    ideal = -(-segments * count // SEGMENTS)
    # Input limit: MFBDriver starts every frame in a new 64 B word.
    input_cycles = -(-size // 64) * count
    efficiency = ideal / stats.transfers
    cocotb.log.info(f"size {size}: {stats.transfers} output cycles ({stats.transfers / count:.3f} per frame), "
                    f"minimum {ideal}, input needs {input_cycles}, efficiency {100 * efficiency:.1f} %, "
                    f"{tb.in_cov.stall_cycles} cycles of IN_MFB_DST_RDY = 0")
    assert stats.frame_gaps == 0, "VALID deasserted inside a frame with continuous input"


@cocotb.test()
async def test_reset(dut: Any) -> None:
    """RESET while a frame is stalled on the output: VALID drops, no fragment of the frame follows the reset."""
    tb = await start(dut, 20)
    rng = random.Random(20)
    first = 50
    for _ in range(first):
        tb.send(bytes(rng.getrandbits(8) for _ in range(rng.randint(MIN_FRAME, 300))))
    await tb.wait_for_frames(first, 50000)

    lost = bytes(rng.getrandbits(8) for _ in range(200))
    tb.send(lost)
    for _ in range(100):
        await RisingEdge(dut.CLK)
        if dut.OUT_SAXIS_VALID.value == 1:
            break
    dut.OUT_SAXIS_READY.value = 0
    for _ in range(100):
        await RisingEdge(dut.CLK)
        if tb.mfb.frame_cnt == first + 1:
            break
    assert tb.mfb.frame_cnt == first + 1, "the input did not accept the whole frame"
    await ClockCycles(dut.CLK, 3)
    assert dut.OUT_SAXIS_VALID.value == 1, "the frame is not stalled on the output"

    dut.RESET.value = 1
    await ClockCycles(dut.CLK, 3)
    assert dut.OUT_SAXIS_VALID.value == 0, "OUT_SAXIS_VALID is not cleared by RESET"
    dut.RESET.value = 0
    tb.expected.remove(lost)
    await ClockCycles(dut.CLK, 10)
    assert dut.OUT_SAXIS_VALID.value == 0, "OUT_SAXIS_VALID set after RESET without a new frame"
    dut.OUT_SAXIS_READY.value = 1
    await ClockCycles(dut.CLK, 10)
    assert dut.OUT_SAXIS_VALID.value == 0, "data of the dropped frame left the adapter after RESET"

    second = 200
    for _ in range(second):
        tb.send(bytes(rng.getrandbits(8) for _ in range(rng.randint(MIN_FRAME, 1518))))
    await tb.wait_for_frames(first + second, 100000)
    tb.check(first + second)


@cocotb.test()
async def test_valid_independent_of_ready(dut: Any) -> None:
    """AXI4-Stream: a source must not wait for TREADY before asserting TVALID.

    A frame sent while OUT_SAXIS_READY = 0 must raise OUT_SAXIS_VALID: the
    output register also loads when it is empty. A sink that waits for VALID
    before it asserts READY would otherwise never receive the frame.
    """
    tb = await start(dut, 30)
    dut.OUT_SAXIS_READY.value = 0
    tb.send(bytes(range(100)))
    await ClockCycles(dut.CLK, 30)
    valid = dut.OUT_SAXIS_VALID.value == 1
    dut.OUT_SAXIS_READY.value = 1
    await tb.wait_for_frames(1, 1000)
    tb.check(1)
    assert valid, "OUT_SAXIS_VALID stays 0 while OUT_SAXIS_READY = 0 although a frame is ready"
