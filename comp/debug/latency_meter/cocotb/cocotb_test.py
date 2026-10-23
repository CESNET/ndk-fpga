# cocotb_test.py: cocotb test of the LATENCY_METER
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

import random
from collections import deque
from dataclasses import dataclass
from typing import Optional

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge

PIPE_STAGES = 3
RESET_CYCLES = 5
META_SETTLE_CYCLES = 4


@dataclass
class Stimulus:
    """Events driven into the meter during one clock cycle"""
    start: bool = False
    start_meta: int = 0
    end: bool = False
    end_meta: int = 0


@dataclass
class Expected:
    """What the meter has to show for one cycle"""
    full: bool = False
    items: int = 0
    vld: bool = False
    latency: int = 0
    start_meta: Optional[int] = None
    end_meta: int = 0


@dataclass
class Observed:
    """What the meter shows at the outputs in one cycle"""
    full: int
    items: int
    vld: int
    latency: int
    start_meta: int
    end_meta: int


class LatencyModel:
    """Cycle-accurate reference of the meter: starts are stored in order, an end pairs with the oldest stored start."""

    def __init__(self, data_width, depth):
        self.mask = 2**data_width - 1
        self.depth = depth
        self.queue = deque()
        self.history = []
        self.heads = []
        self.cycle = 0
        self.accepted = 0
        self.dropped = 0
        self.orphans = 0
        self.claimable = 0

    def is_full(self):
        return len(self.queue) == self.depth

    def step(self, stim):
        """Advance one cycle, return the expected outputs of this cycle and of the registered result"""
        cycle = self.cycle
        full = self.is_full()
        items = len(self.queue)
        empty = items == 0
        head = self.queue[0] if not empty else None
        self.heads.append(None if head is None else head[2])
        self.history.append(stim)

        fin = self.history[cycle - PIPE_STAGES] if cycle >= PIPE_STAGES else Stimulus()
        fin_tick = (cycle - PIPE_STAGES) & self.mask
        result = Expected(full=full, items=items, end_meta=fin.end_meta)
        if fin.end and not empty:
            start_tick, start_meta, start_id, start_cycle = self.queue.popleft()
            result.vld = True
            result.latency = (fin_tick - start_tick) & self.mask
            # The start meta is sampled when the end enters the pipeline, so it is reliable only if the item was already
            # the settled FIFO head then.
            end_cycle = cycle - PIPE_STAGES
            if self.heads[end_cycle] == start_id and start_cycle <= end_cycle - META_SETTLE_CYCLES:
                result.start_meta = start_meta
        elif fin.end:
            self.orphans += 1
            if fin.start:
                result.vld = True
                result.latency = 0

        if stim.start and not full:
            self.queue.append((cycle & self.mask, stim.start_meta, self.accepted, cycle))
            self.accepted += 1
            self.claimable += 1
        elif stim.start:
            self.dropped += 1
        if stim.end and self.claimable > 0:
            self.claimable -= 1
        self.cycle += 1
        return result

    def outstanding(self, start_accepted):
        """Number of accepted starts that have no end issued yet"""
        return self.claimable + (1 if start_accepted else 0)


class Monitor:
    """Samples the meter outputs every cycle"""

    def __init__(self, dut):
        self.dut = dut

    def sample(self):
        dut = self.dut
        return Observed(
            full=int(dut.FIFO_FULL.value),
            items=int(dut.FIFO_ITEMS.value),
            vld=int(dut.LATENCY_VLD.value),
            latency=int(dut.LATENCY.value),
            start_meta=int(dut.LATENCY_START_META.value),
            end_meta=int(dut.LATENCY_END_META.value),
        )


class Scoreboard:
    """Compares the monitored cycles against the reference"""

    def __init__(self):
        self.latencies = 0
        self.meta_checked = 0
        self.meta_skipped = 0
        self.errors = []

    def compare_status(self, cycle, exp, obs):
        if obs.full != int(exp.full):
            self.errors.append(f"cycle {cycle}: FIFO_FULL {obs.full}, expected {int(exp.full)}")
        if obs.items != exp.items:
            self.errors.append(f"cycle {cycle}: FIFO_ITEMS {obs.items}, expected {exp.items}")

    def compare_result(self, cycle, exp, obs):
        if obs.vld != int(exp.vld):
            self.errors.append(f"cycle {cycle}: LATENCY_VLD {obs.vld}, expected {int(exp.vld)}")
            return
        if not exp.vld:
            return
        self.latencies += 1
        if obs.latency != exp.latency:
            self.errors.append(f"cycle {cycle}: LATENCY {obs.latency}, expected {exp.latency}")
        if obs.end_meta != exp.end_meta:
            self.errors.append(f"cycle {cycle}: END_META {obs.end_meta}, expected {exp.end_meta}")
        if exp.start_meta is None:
            self.meta_skipped += 1
        else:
            self.meta_checked += 1
            if obs.start_meta != exp.start_meta:
                self.errors.append(f"cycle {cycle}: START_META {obs.start_meta}, expected {exp.start_meta}")

    def check(self):
        assert not self.errors, f"{len(self.errors)} mismatches, first: {self.errors[:5]}"


class Testbench:
    def __init__(self, dut):
        self.dut = dut
        self.data_width = len(dut.LATENCY)
        self.depth = 2 ** (len(dut.FIFO_ITEMS) - 1)
        self.start_meta_width = len(dut.START_EVENT_META)
        self.end_meta_width = len(dut.END_EVENT_META)
        self.model = LatencyModel(self.data_width, self.depth)
        self.monitor = Monitor(dut)
        self.scoreboard = Scoreboard()
        self.expected = []
        self.next_start_meta = 0
        self.next_end_meta = 0

    async def reset(self):
        dut = self.dut
        cocotb.start_soon(Clock(dut.CLK, 10, unit="ns").start())
        dut.RST.value = 1
        dut.START_EVENT.value = 0
        dut.END_EVENT.value = 0
        dut.START_EVENT_META.value = 0
        dut.END_EVENT_META.value = 0
        for _ in range(RESET_CYCLES):
            await RisingEdge(dut.CLK)
        dut.RST.value = 0

    def start_meta(self):
        self.next_start_meta = (self.next_start_meta + 1) & (2**self.start_meta_width - 1)
        return self.next_start_meta

    def end_meta(self):
        self.next_end_meta = (self.next_end_meta + 1) & (2**self.end_meta_width - 1)
        return self.next_end_meta

    async def cycle(self, start=False, end=False):
        """Drive one cycle of events, model it and check the outputs sampled at the clock edge"""
        stim = Stimulus(start, self.start_meta() if start else 0, end, self.end_meta() if end else 0)
        self.dut.START_EVENT.value = int(stim.start)
        self.dut.START_EVENT_META.value = stim.start_meta
        self.dut.END_EVENT.value = int(stim.end)
        self.dut.END_EVENT_META.value = stim.end_meta
        self.expected.append(self.model.step(stim))
        await RisingEdge(self.dut.CLK)
        # Outputs read at this edge belong to the cycle driven just now; the registered result of cycle k shows one cycle later.
        index = len(self.expected) - 1
        obs = self.monitor.sample()
        self.scoreboard.compare_status(index, self.expected[index], obs)
        if index >= 1:
            self.scoreboard.compare_result(index - 1, self.expected[index - 1], obs)

    async def idle(self, cycles):
        for _ in range(cycles):
            await self.cycle()

    async def drain(self):
        await self.idle(PIPE_STAGES + 4)

    def can_end(self, will_start):
        return self.model.outstanding(will_start and not self.model.is_full()) > 0


async def legal_traffic(tb, cycles, p_start, p_end):
    """Random starts and ends where every end belongs to an accepted start"""
    for _ in range(cycles):
        start = random.random() < p_start
        end = random.random() < p_end and tb.can_end(start)
        await tb.cycle(start, end)


async def overfill_episode(tb):
    """More starts than the FIFO holds, then as many ends as starts were accepted"""
    starts = tb.depth + random.randint(1, 6)
    for _ in range(starts):
        await tb.cycle(start=True, end=False)
    await tb.idle(random.randint(2, 8))
    for _ in range(tb.model.outstanding(False)):
        await tb.cycle(start=False, end=True)


async def orphan_episode(tb):
    """Ends that have no stored start"""
    for _ in range(random.randint(1, 6)):
        await tb.cycle(start=False, end=random.random() < 0.7)


async def setup(dut):
    tb = Testbench(dut)
    await tb.reset()
    cocotb.log.info(f"DATA_WIDTH={tb.data_width} MAX_PARALEL_EVENTS={tb.depth} "
                    f"START_META_WIDTH={tb.start_meta_width} END_META_WIDTH={tb.end_meta_width}")
    return tb


async def finish(tb, expect_latencies=1):
    await tb.drain()
    cocotb.log.info(f"latencies {tb.scoreboard.latencies}, start meta checked {tb.scoreboard.meta_checked} "
                    f"skipped {tb.scoreboard.meta_skipped}, dropped starts {tb.model.dropped}, orphan ends {tb.model.orphans}")
    tb.scoreboard.check()
    assert tb.scoreboard.latencies >= expect_latencies


@cocotb.test()
async def test_legal_traffic(dut):
    """Random traffic in which every end belongs to an accepted start"""
    tb = await setup(dut)
    for _ in range(40):
        await legal_traffic(tb, 200, random.choice([0.05, 0.3, 0.6]), random.choice([0.05, 0.3, 0.9]))
        await tb.drain()
    await finish(tb, 100)


@cocotb.test()
async def test_start_into_full_fifo(dut):
    """Starts past the capacity are dropped and the stored ones stay intact"""
    tb = await setup(dut)
    await tb.idle(5)
    await overfill_episode(tb)
    await tb.drain()
    assert tb.model.dropped > 0
    assert int(dut.FIFO_ITEMS.value) == 0
    # The meter must still work after the overflow.
    await legal_traffic(tb, 100, 0.2, 0.5)
    await finish(tb, tb.depth)


@cocotb.test()
async def test_end_with_empty_fifo(dut):
    """An end without a stored start gives no latency"""
    tb = await setup(dut)
    await tb.idle(5)
    for _ in range(4):
        await orphan_episode(tb)
        await tb.drain()
    assert tb.model.orphans > 0
    assert tb.scoreboard.latencies == 0
    await legal_traffic(tb, 100, 0.2, 0.5)
    await finish(tb)


@cocotb.test()
async def test_random_episodes(dut):
    """Random sequence of legal traffic, overfill and orphan ends separated by idle gaps"""
    tb = await setup(dut)
    for _ in range(80):
        kind = random.choice(["legal", "overfill", "orphan"])
        if kind == "legal":
            await legal_traffic(tb, random.randint(20, 150), random.random(), random.random())
        elif kind == "overfill":
            await overfill_episode(tb)
        else:
            await orphan_episode(tb)
        # Gap that lets a pending end leave the pipeline before the next episode stores a start.
        await tb.drain()
        # Leftover starts are consumed so the next episode begins with a known FIFO state.
        for _ in range(tb.model.outstanding(False)):
            await tb.cycle(end=True)
        await tb.drain()
    assert tb.model.dropped > 0 and tb.model.orphans > 0
    await finish(tb, 100)


@cocotb.test()
async def test_spaced_pairs(dut):
    """Isolated start and end pairs with the metadata of both checked"""
    tb = await setup(dut)
    await tb.idle(5)
    for _ in range(100):
        await tb.cycle(start=True)
        await tb.idle(random.randint(META_SETTLE_CYCLES, 12))
        await tb.cycle(end=True)
        await tb.idle(random.randint(PIPE_STAGES + 1, 12))
    await finish(tb, 100)
    assert tb.scoreboard.meta_checked == tb.scoreboard.latencies
