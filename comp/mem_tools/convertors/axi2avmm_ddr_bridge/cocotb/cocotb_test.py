# cocotb_test.py: Cocotb tests of the AXI-AVMM interface bridge unit
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author: David Beneš <benes@dyna-nic.com>, 2026
#
# SPDX-License-Identifier: BSD-3-Clause

"""Verification of the Avalon-MM to AXI4 DDR bridge.

The main test is one randomized read/write test; the remaining tests cover
situations a random run is not guaranteed to hit reliably, or that need a
specific backpressure pattern on a single AXI channel.
"""

import random
from dataclasses import dataclass
from typing import Any

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge
from cocotb.utils import get_sim_time
from cocotbext.ofm.avmm.transaction import AvalonMMReadRequestTransaction
from cocotbext.ofm.base.generators import ItemRateLimiter

from testbench import CLK_PERIOD_NS, get_testbench

# word address range used by the tests
ADDRESS_LIMIT = 0x400

TIMEOUT_US = 200


def random_burst(tb: Any, rng: random.Random, minimum: int = 1) -> tuple[int, int]:
    """Picks a random word address and a burst length the slave accepts there."""
    while True:
        address = rng.randrange(ADDRESS_LIMIT)
        limit = tb.burst_limit(address)

        if limit >= minimum:
            return address, rng.randint(minimum, limit)


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_read_single(dut: Any, count: int = 60):
    """Single word reads against a memory filled through the backdoor."""
    tb = await get_testbench(dut)
    rng = random.Random(1)

    tb.fill_memory(0, tb.random_words(ADDRESS_LIMIT, rng))

    for _ in range(count):
        await tb.read(rng.randrange(ADDRESS_LIMIT))

    await tb.idle()
    tb.check()


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_read_burst(dut: Any, count: int = 60):
    """Burst reads of a random length."""
    tb = await get_testbench(dut)
    rng = random.Random(2)

    tb.fill_memory(0, tb.random_words(ADDRESS_LIMIT, rng))

    for _ in range(count):
        address, burst = random_burst(tb, rng)
        await tb.read(address, burst_count=burst)

    await tb.idle()
    tb.check()


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_read_backpressure(dut: Any, count: int = 60):
    """Burst reads with the address and the data channel of the slave stalling."""
    tb = await get_testbench(dut)
    rng = random.Random(3)

    tb.fill_memory(0, tb.random_words(ADDRESS_LIMIT, rng))
    tb.set_backpressure(ar=0.5, r=0.4, seed=3)

    for _ in range(count):
        address, burst = random_burst(tb, rng)
        await tb.read(address, burst_count=burst)

    await tb.idle()
    tb.set_backpressure()
    tb.check()


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_write_single(dut: Any, count: int = 40):
    """Single word writes, each starting from an idle bus."""
    tb = await get_testbench(dut)
    rng = random.Random(4)

    for _ in range(count):
        await tb.write(rng.randrange(ADDRESS_LIMIT), tb.random_words(1, rng))
        await tb.idle(5)

    await tb.idle()
    tb.check()


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_write_burst(dut: Any, count: int = 40):
    """Burst writes of a random length."""
    tb = await get_testbench(dut)
    rng = random.Random(5)

    for _ in range(count):
        address, burst = random_burst(tb, rng)
        await tb.write(address, tb.random_words(burst, rng))
        await tb.idle(5)

    await tb.idle()
    tb.check()


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_write_single_word_after_burst(dut: Any):
    """A single word write directly following a burst write.

    The bridge takes a different path through its state machine depending on
    whether a write starts from an idle bus or right after another burst, so
    the transition is exercised explicitly.
    """
    tb = await get_testbench(dut)
    rng = random.Random(6)

    await tb.write(0x10, tb.random_words(4, rng))
    await tb.write(0x20, tb.random_words(1, rng))

    await tb.idle()
    tb.check()


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_write_data_channel_backpressure(dut: Any, count: int = 40):
    """Burst writes while only the write data channel of the slave stalls.

    The address channel stays free, so the address phase completes before the
    first data beat is accepted.
    """
    tb = await get_testbench(dut)
    rng = random.Random(7)

    tb.set_backpressure(w=0.5, seed=7)

    for _ in range(count):
        address, burst = random_burst(tb, rng)
        await tb.write(address, tb.random_words(burst, rng))

    await tb.idle()
    tb.set_backpressure()
    tb.check()


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_write_address_channel_backpressure(dut: Any, count: int = 40):
    """Burst writes while only the write address channel of the slave stalls.

    The mirror of the previous test: the slave is ready for data before it
    accepts the address.
    """
    tb = await get_testbench(dut)
    rng = random.Random(8)

    tb.set_backpressure(aw=0.6, seed=8)

    for _ in range(count):
        address, burst = random_burst(tb, rng)
        await tb.write(address, tb.random_words(burst, rng))

    await tb.idle()
    tb.set_backpressure()
    tb.check()


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_write_read_roundtrip(dut: Any, count: int = 40):
    """Writes followed by reads of the same words through the bridge."""
    tb = await get_testbench(dut)
    rng = random.Random(9)

    bursts = []

    for _ in range(count):
        address, burst = random_burst(tb, rng)
        await tb.write(address, tb.random_words(burst, rng))
        bursts.append((address, burst))

    for address, burst in bursts:
        await tb.read(address, burst_count=burst)

    await tb.idle()
    tb.check()


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_random(dut: Any, count: int = 200):
    """Randomized mix of reads and writes with backpressure on every AXI channel."""
    tb = await get_testbench(dut)
    rng = random.Random(10)

    tb.fill_memory(0, tb.random_words(ADDRESS_LIMIT, rng))
    tb.set_backpressure(aw=0.3, w=0.3, b=0.2, ar=0.3, r=0.2, seed=10)

    for _ in range(count):
        address, burst = random_burst(tb, rng)

        if rng.random() < 0.5:
            await tb.write(address, tb.random_words(burst, rng))
        else:
            await tb.read(address, burst_count=burst)

        await tb.idle(rng.randint(0, 4))

    await tb.idle()
    tb.set_backpressure()
    tb.check()


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_write_back_to_back_bursts(dut: Any):
    """Bursts that follow each other without the master pausing in between.

    The NDK Avalon-MM masters keep the write request asserted from one burst to
    the next, so the bridge never returns to an idle bus between them. The last
    burst of the request is a single word, which is the shortest one possible.
    """
    tb = await get_testbench(dut)
    rng = random.Random(12)

    # 4 + 4 + 1 words, sent as one uninterrupted request
    await tb.write(0x80, tb.random_words(9, rng), burst_count=4)

    await tb.idle()
    tb.check()


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_write_burst_master_pause(dut: Any, count: int = 40):
    """The master pauses in the middle of a write burst.

    Avalon-MM lets a master deassert its write request between the beats of a
    burst and continue later. The bridge has to hold the burst across the gap.
    The write address channel is stalled at the same time, so the pauses fall
    into the window where the bridge is still waiting for AWREADY.
    """
    tb = await get_testbench(dut)
    rng = random.Random(13)

    tb.set_backpressure(aw=0.6, seed=13)

    tb.master.set_idle_generator(ItemRateLimiter(max_idles=4, zero_idles_chance=40))

    for _ in range(count):
        address, burst = random_burst(tb, rng, minimum=2)
        await tb.write(address, tb.random_words(burst, rng))

    await tb.idle()
    tb.set_backpressure()
    tb.check()


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_write_address_accepted_after_last_beat(dut: Any):
    """AWREADY arrives only after the last write data beat was accepted.

    The bridge then waits for the address handshake with the burst already
    finished on the Avalon-MM side, so the master no longer drives
    AMM_BURST_COUNT. Everything the address phase carries has to survive that
    wait, because AWVALID stays asserted the whole time.
    """
    tb = await get_testbench(dut)
    rng = random.Random(14)

    cocotb.start_soon(tb.stall_write_address(10))
    await tb.write(0x10, tb.random_words(4, rng))

    await tb.idle()
    tb.check()


async def settle(dut: Any) -> None:
    """Lets the monitor record the beat of the cycle that has just finished."""
    await ClockCycles(dut.MEM_CLK, 2)


@dataclass
class ThroughputResult:
    """One measured traffic pattern, in the units the report prints."""
    label     : str
    words     : int
    cycles    : float
    per_cycle : float
    gigabytes : float
    gigabits  : float


def throughput_report(results: list, label: str, words: int, nanoseconds: float, word_bytes: int) -> float:
    """Records one throughput result and returns the achieved words per clock cycle."""
    cycles = nanoseconds / CLK_PERIOD_NS
    per_cycle = words / cycles

    results.append(ThroughputResult(
        label=label,
        words=words,
        cycles=cycles,
        per_cycle=per_cycle,
        gigabytes=per_cycle * word_bytes / CLK_PERIOD_NS,
        gigabits=per_cycle * word_bytes * 8 / CLK_PERIOD_NS,
    ))

    return per_cycle


def log_throughput_table(results: list, word_bytes: int) -> None:
    """Prints the collected results as one block, so the numbers are not lost
    among the rest of the run output."""
    clock_mhz = 1000.0 / CLK_PERIOD_NS
    peak_gbps = word_bytes * 8 / CLK_PERIOD_NS

    lines = [
        "=" * 96,
        f"THROUGHPUT  {word_bytes * 8}-bit data bus @ {clock_mhz:.0f} MHz  ->  peak {peak_gbps:.1f} Gb/s ({word_bytes * clock_mhz / 1000:.1f} GB/s), 1 word/cycle",
        "=" * 96,
        f"{'pattern':<32}{'words':>8}{'cycles':>9}{'words/cyc':>11}{'% peak':>9}{'GB/s':>9}{'Gb/s':>9}",
        "-" * 96,
    ]

    for r in results:
        lines.append(f"{r.label:<32}{r.words:>8}{r.cycles:>9.0f}{r.per_cycle:>11.3f}"
                     f"{100 * r.per_cycle:>8.1f}%{r.gigabytes:>9.2f}{r.gigabits:>9.1f}")

    lines.append("=" * 96)

    for line in lines:
        # an empty message crashes the cocotb log formatter, which indexes
        # msg.splitlines()[0] to attach its prefix
        cocotb.log.info("%s", line or " ")


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_throughput(dut: Any, bursts: int = 120):
    """Measures the maximal sustained throughput of the bridge.

    Nothing is allowed to stall: the AXI slave never backpressures and the
    master always has the next word ready, so what is measured is the ceiling
    the bridge itself imposes rather than the ceiling of the traffic pattern.
    One word per clock cycle is the theoretical peak of the Avalon-MM
    interface, which every result is expressed as a percentage of.
    """
    tb = await get_testbench(dut)
    rng = random.Random(15)

    tb.set_backpressure()

    burst = tb.burst_limit(0)

    # Writes, one request so the bursts follow each other with no idle gap.
    written_before = len(tb.monitor.write_beats)
    start = get_sim_time("ns")
    await tb.write(0, tb.random_words(burst * bursts, rng), burst_count=burst)
    elapsed = get_sim_time("ns") - start
    await settle(dut)
    results = []
    write_rate = throughput_report(results, "write, burst=%d" % burst,
                                   len(tb.monitor.write_beats) - written_before,
                                   elapsed, tb.word_bytes)

    await tb.idle()

    # Writes of a single word each, to show the per-transaction overhead.
    written_before = len(tb.monitor.write_beats)
    start = get_sim_time("ns")
    await tb.write(0, tb.random_words(bursts, rng), burst_count=1)
    elapsed = get_sim_time("ns") - start
    await settle(dut)
    single_rate = throughput_report(results, "write, burst=1",
                                    len(tb.monitor.write_beats) - written_before,
                                    elapsed, tb.word_bytes)

    await tb.idle()

    # Reads, all requests queued up front so they pipeline back-to-back.
    expected = burst * bursts
    read_before = len(tb.monitor.read_data)
    start = get_sim_time("ns")

    for index in range(bursts):
        request = AvalonMMReadRequestTransaction()
        request.address = index * burst
        request.burst_count = burst
        tb.master.send_read_request(request)

    while len(tb.monitor.read_data) - read_before < expected:
        await RisingEdge(dut.MEM_CLK)

    read_rate = throughput_report(results, "read, burst=%d, pipelined" % burst,
                                  len(tb.monitor.read_data) - read_before,
                                  get_sim_time("ns") - start, tb.word_bytes)

    log_throughput_table(results, tb.word_bytes)

    await tb.idle()
    tb.check()

    # Deliberately loose floors: they catch a throughput collapse without
    # turning normal variation into a failure.
    assert write_rate > 0.5, f"write throughput collapsed to {write_rate:.3f} words/cycle"
    assert read_rate > 0.5, f"read throughput collapsed to {read_rate:.3f} words/cycle"
    assert single_rate > 0.1, f"single word write throughput collapsed to {single_rate:.3f} words/cycle"


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_write_burst_burstcount_not_held(dut: Any, count: int = 20):
    """The master stops driving address and burstcount after the first beat.

    Avalon-MM defines both only for the first beat of a write burst, and
    constantBurstBehavior is false by default, so a compliant master may leave
    them as don't-care on the remaining beats. The bridge has to decide where
    WLAST goes from a latched copy rather than from the live input.
    """
    tb = await get_testbench(dut, constant_burst=False)
    rng = random.Random(16)

    # Without AW backpressure the burst never goes through ST_WADDR and the
    # latched address and burst count are never used.
    tb.set_backpressure(aw=0.6, seed=16)

    for _ in range(count):
        address, burst = random_burst(tb, rng, minimum=2)
        await tb.write(address, tb.random_words(burst, rng))
        await tb.idle(5)

    await tb.idle()
    tb.check()
