# cocotb_test.py: cocotb verification of HBM_TESTER_MON
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0
"""Random handshakes on every monitored interface of HBM_TESTER_MON under random TIME, counter modes, MON_RESET
and RESET. A cycle model of the monitor gives DONE in every cycle and both counters whenever they settle."""

import random
from dataclasses import dataclass

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import FallingEdge, ReadOnly, RisingEdge

from cocotbext.ofm.ver.backpressure import BackpressureConfig, BackpressureGenerator

CLK_NS = 4
ROUNDS = 1000
# A counter is compared once the model has held its value this many cycles, so a counter that lags the model by a
# fixed register stage still has to reach exactly the same count.
SETTLE_CYCLES = 4

MODE_NAMES = ("rd words", "wr words", "rd latency", "wr latency", "data ok", "data err", "none 6", "none 7")
HANDSHAKES = ("wr", "wr_rsp", "rd_addr", "rd_data")


@dataclass(slots=True)
class Inputs:
    """Everything the monitor samples at one rising edge."""
    reset: int = 1
    mon_reset: int = 0
    time: int = 0
    mode0: int = 0
    mode1: int = 0
    wr_valid: int = 0
    wr_ready: int = 0
    wr_rsp_valid: int = 0
    wr_rsp_ready: int = 0
    rd_addr_valid: int = 0
    rd_addr_ready: int = 0
    rd_data_valid: int = 0
    rd_data_ready: int = 0
    ok_inc: int = 0
    err_inc: int = 0


class MonModel:
    """Cycle model of HBM_TESTER_MON: the window opens on the first registered write data or read address word and
    lasts TIME cycles; latency counts from the first word to its response; counters stop at their MSB."""

    def __init__(self, width):
        self.mask = 2**width - 1
        self.msb = 2**(width - 1)
        self.wr_word = self.wr_rsp_word = self.rd_addr_word = self.rd_data_word = 0
        self.ok_reg = self.err_reg = 0
        self.busy = self.run_reg = self.rd_lat = self.wr_lat = 0
        self.time_cnt = 0
        self.cnt = [0, 0]
        self.incs = [0] * 8

    def done(self, time):
        return int(self.time_cnt == time)

    def step(self, x):
        """Advances the model by one rising edge with the inputs sampled at that edge."""
        start = self.wr_word | self.rd_addr_word
        run = self.run_reg | (start & (1 - self.busy))
        done = self.done(x.time)
        window = run & (1 - done)
        clear = x.reset | x.mon_reset

        incs = self.incs
        incs[0] = self.rd_data_word & window
        incs[1] = self.wr_word & window
        incs[2] = self.rd_lat
        incs[3] = self.wr_lat
        incs[4] = self.ok_reg & window
        incs[5] = self.err_reg & window

        for k, mode in enumerate((x.mode0, x.mode1)):
            if clear:
                self.cnt[k] = 0
            elif incs[mode] and not self.cnt[k] & self.msb:
                self.cnt[k] += 1

        if x.reset or self.rd_data_word:
            rd_lat = 0
        else:
            rd_lat = 1 if (self.rd_addr_word and not self.busy) else self.rd_lat
        if x.reset or self.wr_rsp_word:
            wr_lat = 0
        else:
            wr_lat = 1 if (self.wr_word and not self.busy) else self.wr_lat

        if x.reset or done:
            self.run_reg = 0
        elif start and not self.busy:
            self.run_reg = 1
        if clear:
            self.time_cnt = 0
        elif run and not done:
            self.time_cnt = (self.time_cnt + 1) & self.mask
        self.busy = 0 if clear else (1 if start else self.busy)
        self.rd_lat, self.wr_lat = rd_lat, wr_lat

        self.wr_word = x.wr_valid & x.wr_ready
        self.wr_rsp_word = x.wr_rsp_valid & x.wr_rsp_ready
        self.rd_addr_word = x.rd_addr_valid & x.rd_addr_ready
        self.rd_data_word = x.rd_data_valid & x.rd_data_ready
        self.ok_reg = x.ok_inc
        self.err_reg = x.err_inc


class Handshake:
    """VALID and READY of one interface, each a BackpressureGenerator whose duty cycle is redrawn every round:
    saturated, idle or anything between."""

    def __init__(self):
        self.cfg = [BackpressureConfig(1, 60, 0.0), BackpressureConfig(1, 60, 0.0)]
        self.bits = [BackpressureGenerator(cfg).levels() for cfg in self.cfg]
        self.enabled = True

    def redraw(self, rng):
        for cfg in self.cfg:
            cfg.low_prob = rng.choice((0.0, 1.0, rng.random(), rng.random()))

    def next(self):
        valid = next(self.bits[0])
        return (valid if self.enabled else 0), next(self.bits[1])


class MonBench:
    def __init__(self, dut):
        self.dut = dut
        self.log = dut._log
        self.width = len(dut.CS_MONITOR_TIME)
        self.rng = random.Random(cocotb.RANDOM_SEED)
        self.model = MonModel(self.width)
        self.x = Inputs()
        self.hs = {name: Handshake() for name in HANDSHAKES}
        self.ok_ratio = 1.0
        self.cycle = 0
        self.stable = [0, 0]
        self.last = [0, 0]
        self.cov = {"compares": 0, "done_cycles": 0, "saturated": 0, "zero_time": 0, "rd_first": 0}
        self.counted = [0] * 8

    def drive(self):
        dut, x = self.dut, self.x
        dut.RESET.value = x.reset
        dut.CS_MONITOR_RESET.value = x.mon_reset
        dut.CS_MONITOR_TIME.value = x.time
        dut.CS_COUNTER0_MODE.value = x.mode0
        dut.CS_COUNTER1_MODE.value = x.mode1
        dut.WR_VALID.value = x.wr_valid
        dut.WR_READY.value = x.wr_ready
        dut.WR_RSP_VALID.value = x.wr_rsp_valid
        dut.WR_RSP_READY.value = x.wr_rsp_ready
        dut.RD_ADDR_VALID.value = x.rd_addr_valid
        dut.RD_ADDR_READY.value = x.rd_addr_ready
        dut.RD_DATA_VALID.value = x.rd_data_valid
        dut.RD_DATA_READY.value = x.rd_data_ready
        dut.GEN_DATA_OK_INC.value = x.ok_inc
        dut.GEN_DATA_ERR_INC.value = x.err_inc

    def randomize_traffic(self):
        x = self.x
        x.wr_valid, x.wr_ready = self.hs["wr"].next()
        x.wr_rsp_valid, x.wr_rsp_ready = self.hs["wr_rsp"].next()
        x.rd_addr_valid, x.rd_addr_ready = self.hs["rd_addr"].next()
        x.rd_data_valid, x.rd_data_ready = self.hs["rd_data"].next()
        # The generator checks every accepted read data word, so OK or ERR pulses with each of them.
        rd_word = x.rd_data_valid & x.rd_data_ready
        ok = int(self.rng.random() < self.ok_ratio)
        x.ok_inc, x.err_inc = rd_word & ok, rd_word & (1 - ok)

    def silence(self):
        x = self.x
        x.wr_valid = x.wr_rsp_valid = x.rd_addr_valid = x.rd_data_valid = 0
        x.ok_inc = x.err_inc = 0

    async def cycle_once(self):
        """Drives self.x for one cycle, steps the model and checks the DUT after the edge."""
        dut, model = self.dut, self.model
        await FallingEdge(dut.CLK)
        self.drive()
        await RisingEdge(dut.CLK)
        model.step(self.x)
        await ReadOnly()
        self.cycle += 1
        for i, inc in enumerate(model.incs):
            self.counted[i] += inc

        exp_done = model.done(self.x.time)
        got_done = int(dut.CS_MONITOR_DONE.value)
        assert got_done == exp_done, f"cycle {self.cycle}: DONE {got_done}, model {exp_done} ({self.state()})"
        self.cov["done_cycles"] += exp_done

        outs = (dut.CS_COUNTER0_OUT, dut.CS_COUNTER1_OUT)
        for k in range(2):
            exp = model.cnt[k]
            if exp != self.last[k]:
                self.last[k] = exp
                self.stable[k] = 0
                continue
            self.stable[k] += 1
            if self.stable[k] >= SETTLE_CYCLES:
                got = outs[k].value.to_unsigned()
                assert got == exp, (f"cycle {self.cycle}: counter {k} ({MODE_NAMES[(self.x.mode0, self.x.mode1)[k]]})"
                                    f" {got}, model {exp} ({self.state()})")
                self.cov["compares"] += 1
                if exp & model.msb:
                    self.cov["saturated"] += 1

    def state(self):
        m = self.model
        return (f"time_cnt {m.time_cnt}, TIME {self.x.time}, busy {m.busy}, run_reg {m.run_reg}, "
                f"rd_lat {m.rd_lat}, wr_lat {m.wr_lat}, modes {self.x.mode0}/{self.x.mode1}")

    def random_time(self):
        rng, top = self.rng, 2**self.width - 1
        kind = rng.random()
        if kind < 0.05:
            return 0
        if kind < 0.25:
            return rng.randint(1, 20)
        if kind < 0.80:
            return rng.randint(20, min(top, 300))
        if kind < 0.90 and self.width <= 10:
            return top
        return rng.randint(0, min(top, 2000))

    async def run_round(self):
        rng, x = self.rng, self.x

        # Counter configuration changes while the bus is idle, as the software does it.
        self.silence()
        x.time = self.random_time()
        x.mode0, x.mode1 = rng.randrange(8), rng.randrange(8)
        self.ok_ratio = rng.choice((1.0, 0.0, rng.random()))
        for hs in self.hs.values():
            hs.redraw(rng)
        self.cov["zero_time"] += x.time == 0
        if rng.random() < 0.03:
            x.reset = 1
            for _ in range(rng.randint(1, 3)):
                await self.cycle_once()
            x.reset = 0
        if rng.random() < 0.9:
            x.mon_reset = 1
            for _ in range(rng.randint(1, 4)):
                await self.cycle_once()
            x.mon_reset = 0
        for _ in range(rng.randint(0, 5)):
            await self.cycle_once()

        # The window opens on a read address word alone in a part of the rounds, the only way read latency counts.
        rd_first = rng.random() < 0.3
        self.cov["rd_first"] += rd_first
        if rd_first:
            for name in ("wr", "rd_data", "wr_rsp"):
                self.hs[name].enabled = False

        duration = rng.randint(1, x.time + x.time // 2 + 50)
        for i in range(duration):
            if rd_first and i == 8:
                for name in ("wr", "rd_data", "wr_rsp"):
                    self.hs[name].enabled = True
            self.randomize_traffic()
            if rng.random() < 0.002:
                x.mon_reset = 1
            elif x.mon_reset and rng.random() < 0.5:
                x.mon_reset = 0
            if rng.random() < 0.01:
                x.mode0, x.mode1 = rng.randrange(8), rng.randrange(8)
            await self.cycle_once()
            if rng.random() < 0.01:
                self.silence()
                for hs in self.hs.values():
                    hs.redraw(rng)
                for _ in range(rng.randint(1, 30)):
                    await self.cycle_once()
        for name in ("wr", "rd_data", "wr_rsp"):
            self.hs[name].enabled = True
        x.mon_reset = 0
        self.silence()
        for _ in range(rng.randint(SETTLE_CYCLES + 1, 40)):
            await self.cycle_once()


@cocotb.test()
async def run_random_test(dut):
    cocotb.start_soon(Clock(dut.CLK, CLK_NS, unit="ns").start())
    tb = MonBench(dut)
    tb.log.info(f"CNT_WIDTH {tb.width}, {ROUNDS} rounds")

    tb.x.reset = 1
    for _ in range(5):
        await tb.cycle_once()
    tb.x.reset = 0

    for _ in range(ROUNDS):
        await tb.run_round()

    counted = ", ".join(f"{name} {n}" for name, n in zip(MODE_NAMES, tb.counted))
    tb.log.info(f"summary: {tb.cycle} cycles, {tb.cov}, increments: {counted}")
    assert tb.cov["compares"] > ROUNDS, "too few settled counter values were compared"
    assert tb.cov["done_cycles"] > 0 and tb.cov["zero_time"] > 0 and tb.cov["rd_first"] > 0
    assert all(n > 0 for n in tb.counted[:6]), f"a counter mode never incremented: {counted}"
    if tb.width <= 10:
        assert tb.cov["saturated"] > 0, "no counter reached its saturation"
