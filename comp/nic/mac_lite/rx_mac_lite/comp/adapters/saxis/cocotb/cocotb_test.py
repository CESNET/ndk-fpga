# cocotb_test.py: Cocotb tests of RX_MAC_LITE_ADAPTER_SAXIS
# Copyright (C) 2026 DynaNIC Semiconductors, Ltd.
# Author(s): Vlastimil Kosar <kosar@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Verification of RX_MAC_LITE_ADAPTER_SAXIS (DCMAC Segmented AXI-Stream -> MFB 1,2*SEGMENTS,8,8).

The main test is one randomized test run in several scenarios of DCMAC
timing and frame errors, plus one scenario beyond PG369 (idle segments
between frames). The remaining tests cover all frame lengths and positions,
frames shorter than the DCMAC minimum, the placement of ERR, the latency and
the reset.
"""

import os
import random
from typing import Any

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, RisingEdge

from testbench import Testbench

# 200G DCMAC core clock 390.625 MHz
CLK_PERIOD_PS = 2560
SEGMENT_BYTES = 16
# Smallest frame the DCMAC delivers, shorter ones are dropped in the DCMAC.
DCMAC_MIN_FRAME = 64
FRAMES = int(os.environ.get("COCOTB_TRANSACTIONS", "3000"))

# (idle mode, rate %, probability of VALID gaps inside frames, ERR probability, frames up to 9600 B)
SCENARIOS = {
    "back_to_back":    ("cycle", 0, 0.0, 0.1, False),
    "idles_and_gaps":  ("cycle", 60, 0.2, 0.2, False),
    "errors":          ("cycle", 80, 0.1, 0.5, False),
    "jumbo":           ("cycle", 0, 0.1, 0.1, True),
    "segment_idles":   ("segment", 70, 0.0, 0.2, False),
}


def min_safe_frame(segments: int) -> int:
    """Shortest frame that never puts two SOPs or two EOPs into one cycle.

    A frame of up to segments - 1 segments can start and end between the EOP of
    one frame and the SOP of another in a single cycle; MFB with one region
    carries only one SOF and one EOF per word.
    """
    return (segments - 1) * SEGMENT_BYTES + 1


async def start(dut: Any, **kwargs: Any) -> Testbench:
    cocotb.start_soon(Clock(dut.CLK, CLK_PERIOD_PS, unit="ps").start())
    dut.RESET.value = 1
    tb = Testbench(dut, **kwargs)
    await tb.reset()
    return tb


@cocotb.test()
@cocotb.parametrize(scenario=list(SCENARIOS))
async def test_random(dut: Any, scenario: str) -> None:
    """Random frames from 64 B with DCMAC idles, VALID gaps inside frames and ERR; checks data, order and ERROR."""
    idle_mode, rate, gap_prob, err_prob, jumbo = SCENARIOS[scenario]
    seed = list(SCENARIOS).index(scenario) + 1
    rng = random.Random(seed)
    random.seed(seed)
    tb = await start(dut, idle_mode=idle_mode, rate_percentage=rate, inner_gap_prob=gap_prob)
    segments = tb.segments

    count = FRAMES // 3 if jumbo else FRAMES
    for _ in range(count):
        if jumbo and rng.random() < 0.1:
            size = rng.randint(1519, 9600)
        elif rng.random() < 0.3:
            size = rng.randint(DCMAC_MIN_FRAME, DCMAC_MIN_FRAME + 2 * segments * SEGMENT_BYTES)
        else:
            size = rng.randint(DCMAC_MIN_FRAME, 1518)
        tb.send(bytes(rng.getrandbits(8) for _ in range(size)), err=rng.random() < err_prob)

    await tb.wait_for_frames(count, 600 * count)
    compliant = idle_mode == "cycle"
    tb.check(count, compliant=compliant)

    stats = tb.checker.stats
    assert len(stats.mty) == 16, f"MTY values not covered: {sorted(set(range(16)) - set(stats.mty))}"
    assert set(stats.eop_pos) == set(range(segments)), "EOP not covered in every segment"
    assert set(stats.sop_pos) == set(range(segments)), "SOP not covered in every segment"
    assert stats.eop_sop_cycles > 0, "no cycle with the end of a frame and the start of another one"
    if gap_prob:
        assert stats.frame_gaps > 0, "no VALID gap inside a frame"
    if not compliant:
        assert tb.checker.violations, "the segment idles did not produce placements beyond PG369"


@cocotb.test()
async def test_frame_lengths(dut: Any) -> None:
    """Every length from 64 B over three cycles, back to back so that each starts in every segment."""
    tb = await start(dut)
    segments = tb.segments
    rng = random.Random(10)
    count = 0
    for size in range(DCMAC_MIN_FRAME, DCMAC_MIN_FRAME + 3 * segments * SEGMENT_BYTES + 1):
        for _ in range(2 * segments):
            tb.send(bytes(rng.getrandbits(8) for _ in range(size)), err=rng.random() < 0.2)
            count += 1
    await tb.wait_for_frames(count, 100 * count)
    tb.check(count)
    assert set(tb.checker.stats.sop_pos) == set(range(segments))


@cocotb.test()
async def test_short_frames(dut: Any) -> None:
    """Frames shorter than the DCMAC minimum down to the shortest one the MFB output can carry.

    The DCMAC drops frames below 64 B, so this only shows the margin of the
    adapter. Shorter frames than min_safe_frame() need two SOFs or EOFs in one
    MFB word and are not supported.
    """
    tb = await start(dut, min_segments=1)
    rng = random.Random(20)
    count = 0
    for size in range(min_safe_frame(tb.segments), DCMAC_MIN_FRAME):
        for _ in range(4 * tb.segments):
            tb.send(bytes(rng.getrandbits(8) for _ in range(size)), err=rng.random() < 0.2)
            count += 1
    await tb.wait_for_frames(count, 100 * count)
    tb.check(count)


async def drive_cycle(dut: Any, segments: int, data: list[int], ena: int, sop: int = 0, eop: int = 0,
                      err: int = 0, mty: int = 0, eop_seg: int = 0) -> None:
    for i in range(segments):
        dut.IN_SAXIS_DATA[i].value = data[i]
        dut.IN_SAXIS_MTY[i].value = mty if i == eop_seg else 0
    dut.IN_SAXIS_ENA.value = ena
    dut.IN_SAXIS_SOP.value = sop
    dut.IN_SAXIS_EOP.value = eop
    dut.IN_SAXIS_ERR.value = err
    dut.IN_SAXIS_VALID.value = 1
    await RisingEdge(dut.CLK)
    dut.IN_SAXIS_VALID.value = 0
    dut.IN_SAXIS_ENA.value = 0
    dut.IN_SAXIS_SOP.value = 0
    dut.IN_SAXIS_EOP.value = 0
    dut.IN_SAXIS_ERR.value = 0


@cocotb.test()
async def test_error_placement(dut: Any) -> None:
    """OUT_MFB_ERROR follows ERR of the EOP segment only, EOF_POS follows the EOP segment and its MTY.

    ERR in other enabled segments, SOP, EOP and ERR in disabled segments and
    all of them in a cycle with VALID = 0 must not mark or end the frame.
    Driven directly, the driver sets these bits only where PG369 allows them.
    """
    cocotb.start_soon(Clock(dut.CLK, CLK_PERIOD_PS, unit="ps").start())
    segments = len(dut.IN_SAXIS_SOP)
    full = (1 << segments) - 1
    for name in ("ENA", "SOP", "EOP", "ERR", "VALID"):
        getattr(dut, f"IN_SAXIS_{name}").value = 0
    dut.RESET.value = 1
    await ClockCycles(dut.CLK, 3)
    dut.RESET.value = 0
    await RisingEdge(dut.CLK)

    rng = random.Random(30)
    results = []
    for eop_seg in range(segments):
        for case in ("eop", "other_segments", "disabled_segments", "valid_low", "none"):
            ena_last = (1 << (eop_seg + 1)) - 1
            mty = rng.randint(0, 15)
            err = {"eop": 1 << eop_seg, "other_segments": ena_last & ~(1 << eop_seg),
                   "disabled_segments": full & ~ena_last, "valid_low": 0, "none": 0}[case]
            disabled = full & ~ena_last if case == "disabled_segments" else 0
            await drive_cycle(dut, segments, [rng.getrandbits(128) for _ in range(segments)], full, sop=1)
            if case == "valid_low":
                dut.IN_SAXIS_ERR.value = full
                dut.IN_SAXIS_EOP.value = full
                dut.IN_SAXIS_SOP.value = full
                dut.IN_SAXIS_ENA.value = full
                await RisingEdge(dut.CLK)
            await drive_cycle(dut, segments, [rng.getrandbits(128) for _ in range(segments)], ena_last,
                              sop=disabled, eop=(1 << eop_seg) | disabled, err=err, mty=mty, eop_seg=eop_seg)
            await RisingEdge(dut.CLK)
            sampled = None
            for _ in range(3):
                if dut.OUT_MFB_SRC_RDY.value == 1 and dut.OUT_MFB_EOF.value == 1:
                    sampled = dut.OUT_MFB_ERROR.value == 1
                    eof_pos = dut.OUT_MFB_EOF_POS.value.to_unsigned()
                    break
                await RisingEdge(dut.CLK)
            expected = case == "eop"
            assert sampled is not None, f"EOP in segment {eop_seg}, case {case}: no EOF on OUT_MFB"
            assert eof_pos == eop_seg * SEGMENT_BYTES + 15 - mty, f"EOF_POS {eof_pos} for EOP in segment {eop_seg}, MTY {mty}"
            results.append((eop_seg, case, sampled))
            assert sampled == expected, f"EOP in segment {eop_seg}, ERR case {case}: OUT_MFB_ERROR = {int(sampled)}"
    cocotb.log.info(f"{len(results)} ERR placements checked")


@cocotb.test()
async def test_latency_and_reset(dut: Any) -> None:
    """OUT_MFB_SRC_RDY follows IN_SAXIS_VALID after one cycle and is held low during RESET."""
    cocotb.start_soon(Clock(dut.CLK, CLK_PERIOD_PS, unit="ps").start())
    segments = len(dut.IN_SAXIS_SOP)
    full = (1 << segments) - 1
    dut.IN_SAXIS_ENA.value = full
    dut.IN_SAXIS_SOP.value = 0
    dut.IN_SAXIS_EOP.value = 0
    dut.IN_SAXIS_ERR.value = 0
    dut.IN_SAXIS_VALID.value = 1
    dut.RESET.value = 1
    await ClockCycles(dut.CLK, 5)
    assert dut.OUT_MFB_SRC_RDY.value == 0, "OUT_MFB_SRC_RDY = 1 during RESET"

    dut.RESET.value = 0
    rng = random.Random(40)
    pattern = [rng.random() < 0.5 for _ in range(200)]
    history = []
    for valid in pattern:
        dut.IN_SAXIS_VALID.value = int(valid)
        await RisingEdge(dut.CLK)
        history.append(dut.OUT_MFB_SRC_RDY.value == 1)
    # history[k] is sampled at the edge that registers pattern[k], so it shows pattern[k - 1].
    assert history[1:] == pattern[:-1], "OUT_MFB_SRC_RDY is not IN_SAXIS_VALID delayed by one cycle"
