# cocotb_test.py: Component-level verification of PTC_TAG_MANAGER
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, RisingEdge

from testbench import Testbench, DmaUphdr, TYPE_READ, TYPE_WRITE, unpack_item, Heartbeat


@cocotb.test()
async def test_write_before_read_at_last_free_tag(dut):
    """
    Regression for a write that precedes a read in one MVB group while a single tag
    is left free.

    The test is deterministic, without randomization and without backpressure. The
    state of the tag pool and the layout of the MVB lanes are therefore controlled
    directly. The test first allocates tags by reads in lane 0 alone, until one tag
    is left free. The lane index equals rd_ptr in this phase, which gives the
    baseline latency. Then it presents one MVB group with a write in lane 0 and a
    read in lane 1. The write takes no tag, so the read has rd_ptr 0 and lane index
    1. FIFOX_MULTI compacts EMPTY towards port 0, so it reports port 1 as empty
    while one item is left. Reading the empty flag by the lane index would therefore
    block the whole UP pipeline. auto_assign_rdy therefore checks the last port
    that the group really reads.
    """
    if int(dut.MVB_UP_ITEMS.value) < 2:
        cocotb.log.info("needs at least 2 UP lanes for write in lane 0 and read in lane 1 - skipping")
        return
    if int(dut.CHECK_CPL_CREDITS.value):
        # Allocating the whole pool without completing anything needs the tag pool to
        # be the only limit. With CHECK_CPL_CREDITS on and EXTRA_WORDS small, the word
        # budget stops the requests long before the tags run out.
        cocotb.log.info(
            "CHECK_CPL_CREDITS is on, the word budget would stop the requests before "
            "the tags run out - skipping")
        return
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())
    mvb_up_items = int(dut.MVB_UP_ITEMS.value)
    uphdr_width = len(DmaUphdr())
    pool_size = 512 if int(dut.PCIE_TAG_WIDTH.value) == 10 else 256

    dut.RESET.value = 1
    dut.MVB_UP_HDR_IN_SRC_RDY.value = 0
    dut.MVB_UP_HDR_IN_VLD.value = 0
    dut.MVB_UP_HDR_IN.value = 0
    dut.RCB_SIZE.value = 0
    dut.TAG_VLD.value = 0
    dut.TAG_RELEASE.value = 0
    dut.MVB_UP_HDR_OUT_DST_RDY.value = 1  # no output backpressure, keeps timing deterministic
    await ClockCycles(dut.CLK, 10)
    dut.RESET.value = 0
    await RisingEdge(dut.CLK)

    def make_hdr(is_write: bool, tag: int, unitid: int) -> DmaUphdr:
        return DmaUphdr(
            dma_request_length=1,
            dma_request_type=TYPE_WRITE if is_write else TYPE_READ,
            dma_request_firstib=0, dma_request_lastib=0,
            dma_request_tag=tag, dma_request_unitid=unitid,
            dma_request_global=0, dma_request_vfid=0, dma_request_relaxed=0,
        )

    async def submit_group(lane_hdrs: dict) -> None:
        """Present one MVB group, given as a map from lane to header, until DST_RDY."""
        vlds = 0
        word = 0
        for lane, hdr in lane_hdrs.items():
            vlds |= 1 << lane
            word |= hdr.serialize() << (lane * uphdr_width)
        dut.MVB_UP_HDR_IN_SRC_RDY.value = 1
        dut.MVB_UP_HDR_IN_VLD.value = vlds
        dut.MVB_UP_HDR_IN.value = word
        while True:
            await RisingEdge(dut.CLK)
            if int(dut.MVB_UP_HDR_IN_DST_RDY.value) == 1:
                break
        dut.MVB_UP_HDR_IN_SRC_RDY.value = 0
        dut.MVB_UP_HDR_IN_VLD.value = 0

    async def wait_for_admission(expect_tag: int, expect_type: int, timeout: int):
        """Return the clock cycles until a matching item is on MVB_UP_HDR_OUT, else None."""
        for cyc in range(1, timeout + 1):
            await RisingEdge(dut.CLK)
            if int(dut.MVB_UP_HDR_OUT_SRC_RDY.value) != 1:
                continue
            vld = int(dut.MVB_UP_HDR_OUT_VLD.value)
            if vld == 0:
                continue
            hdr_word = int(dut.MVB_UP_HDR_OUT.value)
            for lane in range(mvb_up_items):
                if not (vld >> lane) & 1:
                    continue
                hdr = DmaUphdr.deserialize(unpack_item(hdr_word, uphdr_width, lane))
                if hdr.dma_request_type == expect_type and hdr.dma_request_tag == expect_tag:
                    return cyc
        return None

    while int(dut.PCIE_TAG_STATUS.value) < pool_size:
        await RisingEdge(dut.CLK)

    # Allocate a known number of tags instead of polling PCIE_TAG_STATUS in the loop.
    # That signal is registered one clock cycle after the read of the FIFO. Reading it
    # right after wait_for_admission returns would give the value from before the read.
    baseline_latency = None
    for read_idx in range(pool_size - 1):
        await submit_group({0: make_hdr(False, read_idx % 256, 0)})
        baseline_latency = await wait_for_admission(read_idx % 256, TYPE_READ, 100)
        assert baseline_latency is not None, f"read {read_idx} never admitted"

    for _ in range(5):
        await RisingEdge(dut.CLK)
    status = int(dut.PCIE_TAG_STATUS.value)
    assert status == 1, f"expected exactly 1 free tag after {pool_size - 1} reads, got {status}"
    cocotb.log.info(f"exactly 1 free tag left, baseline single read latency={baseline_latency} cycles")

    write_hdr = make_hdr(True, 0, 0)
    read_hdr = make_hdr(False, 123, 1)
    await submit_group({0: write_hdr, 1: read_hdr})
    latency = await wait_for_admission(123, TYPE_READ, timeout=100)
    cocotb.log.info(f"write then read group: latency={latency} (baseline={baseline_latency})")

    assert latency is not None, (
        "the read was never admitted within the timeout, auto_assign_rdy checks the "
        "empty flag of a port that is not read")
    assert latency == baseline_latency, (
        f"read behind a write in the same group took {latency} cycles to be admitted, "
        f"an equivalent single read took {baseline_latency}")


@cocotb.test()
async def test_random_traffic(dut, reads_to_complete=20000):
    """
    Random mix of read and write requests with out-of-order, multi-chunk completions.

    Every allocated tag, every write placeholder tag and every DMA Tag and ID that
    the DUT returns on the DOWN side is checked against the model.

    The "credit_check" combination of ver_settings.py sets CHECK_CPL_CREDITS. The test
    then also covers the word budget of the Storage FIFOX. The model repeats the
    reservation and the release of free_cplh_reg on the same traffic. It reports a
    read that the DUT admits over the budget.
    """
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())

    tb = Testbench(dut)
    await tb.reset()
    tb.start()

    if tb.model.check_cpl_credits:
        # The small budget is what this combination tests. It also limits how many
        # reads run at once, so each read needs far more clock cycles than in the
        # other combinations. The check below only needs the budget to be reached.
        reads_to_complete = min(reads_to_complete, 1000)

    last_logged = 0
    heartbeat = Heartbeat()
    while tb.reads_completed < reads_to_complete:
        if tb.reads_completed - last_logged >= 1000:
            last_logged = tb.reads_completed
            cocotb.log.info(f"reads completed: {tb.reads_completed}/{reads_to_complete}")
        heartbeat.tick(
            reads_completed=f"{tb.reads_completed}/{reads_to_complete}",
            in_flight=len(tb.model.in_flight),
            free=len(tb.model.free),
            outstanding_words=tb.model.outstanding_words,
        )
        await ClockCycles(dut.CLK, 200)

    # Check that the word budget really was the limit. A model that reserves too few
    # words would pass without this check. Each read reserves at least one word, so a
    # budget as large as the whole tag pool never limits anything and the check is
    # skipped.
    if tb.model.check_cpl_credits and tb.model.available_words < tb.model.pool_size:
        def check_budget_was_reached():
            margin = tb.model.available_words - tb.model.max_outstanding_words
            assert margin <= 4, (
                f"the CplD word budget was never reached, the peak reservation was "
                f"{tb.model.max_outstanding_words}/{tb.model.available_words} words")
        tb.scoreboard.check(check_budget_was_reached)

    tb.scoreboard.raise_if_errors()
