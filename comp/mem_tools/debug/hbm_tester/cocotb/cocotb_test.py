# cocotb_test.py: cocotb verification of HBM_TESTER
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0
"""HBM_TESTER with a cocotbext-axi memory on every port and MI_CLK asynchronous to HBM_CLK. Back-to-back MI
requests are checked against a register model; generator runs are checked against the AXI handshakes the bench
counted on every port."""

import logging
import random
from collections import deque
from dataclasses import dataclass, field

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, Event, RisingEdge, Timer
from cocotbext.axi import AxiBus, AxiRam

from cocotbext.ofm.mi.drivers import MIPipelinedDriver
from cocotbext.ofm.mi.monitors import MIMonitor
from cocotbext.ofm.mi.transaction import MiTransactionType
from cocotbext.ofm.ver.backpressure import BackpressureConfig, BackpressureGenerator

HBM_CLK_PS = 4000
VERSION = 0x20240119
DEAD2BAD = 0xDEAD2BAD
DEADCAFE = 0xDEADCAFE

REG_VERSION = 0x00
REG_RUN = 0x10
REG_CONFIG = 0x14
REG_MON_RESET = 0x18
REG_TIME = 0x1C
REG_DONE = 0x20
REG_STAT = 0x200
RW_REGS = (REG_RUN, REG_CONFIG, REG_MON_RESET, REG_TIME)
PAUSE_RATES = (0.0, 0.2, 0.5, 0.8)
RESET_VALUES = {REG_RUN: 0, REG_CONFIG: 0, REG_MON_RESET: 0, REG_TIME: 0x0000FFFF}

CFG_CONNECT = 0x1
CFG_RAND_ADDR = 0x2
CFG_RW_SWITCH = 0x8
CFG_BL8 = 0x40
CFG_NO_WAIT = 0x80
CFG_AXI_ID = 0x10000
RUN_WR, RUN_RD, RUN_RW = 1, 2, 3
MODE_RD_WORDS, MODE_WR_WORDS, MODE_RD_LAT, MODE_WR_LAT, MODE_DATA_OK, MODE_DATA_ERR = range(6)

# A TIME write reaches the DONE register through the port and ADC registers; reads this soon after it may see either.
DONE_SETTLE_PS = 40 * HBM_CLK_PS
# Upper bound of the HSI-to-AXI pipe latencies the bench allows when it derives a counter from AXI handshakes.
MAX_PIPE_OFFSET = 8


def config(run_mode, cnt0, cnt1, flags=0):
    return CFG_CONNECT | flags | (run_mode << 4) | (cnt0 << 8) | (cnt1 << 12)


class ArmedPause:
    """Pause generator of one AXI channel: no pause until the first VALID of a run arms it, so the backpressure keeps
    the same alignment to the generator traffic whatever the MI latency of the request that started it."""

    def __init__(self, bench):
        self.bench = bench
        self.bits = None
        self.armed_run = None
        self.paused = False

    def __iter__(self):
        return self

    def __next__(self):
        b = self.bench
        if b.freeze:
            self.paused = True
        elif not b.armed:
            self.paused = False
        else:
            if self.armed_run != b.run_id:
                self.armed_run = b.run_id
                self.bits = BackpressureGenerator(BackpressureConfig(1, 12, b.pause_rate)).levels()
            self.paused = not next(self.bits)
        return self.paused


@dataclass
class MiOp:
    write: bool
    addr: int
    data: int = 0
    expected: tuple = ()
    value: int = None
    done: Event = field(default_factory=Event)


class RegModel:
    """MI register map of HBM_TESTER. A read is predicted from the writes accepted before it; DONE and the counters
    are only predicted while no generator is connected."""

    def __init__(self, ports, cnt_width):
        self.ports = ports
        self.cnt_mask = 2**cnt_width - 1
        self.regs = dict(RESET_VALUES)
        self.init_done = False
        self.static = True
        # (time of the write, TIME value it replaced) of recent TIME writes
        self.old_times = deque()

    def done_vector(self, time):
        return (2**self.ports - 1) if (time & self.cnt_mask) == 0 else 0

    def write(self, addr, data, now_ps):
        if not self.init_done:
            return
        reg = addr & 0xFFF
        if reg in RW_REGS:
            if reg == REG_TIME:
                self.old_times.append((now_ps, self.regs[REG_TIME]))
            self.regs[reg] = data

    def read(self, addr, now_ps):
        """Acceptable read values, or () where the value depends on the traffic."""
        if not self.init_done:
            return (DEAD2BAD,)
        reg = addr & 0xFFF
        group, low = reg >> 9, reg & 0xFF
        if group == 0:
            if low == REG_VERSION:
                return (VERSION,)
            if low in RW_REGS:
                return (self.regs[low],)
            if low == REG_DONE:
                if not self.static:
                    return ()
                while self.old_times and now_ps - self.old_times[0][0] >= DONE_SETTLE_PS:
                    self.old_times.popleft()
                times = [self.regs[REG_TIME]] + [t for _, t in self.old_times]
                return tuple({self.done_vector(t) for t in times})
            return (DEADCAFE,)
        if group == 1 and (reg & 0xF) in (0x0, 0x4):
            return (0,) if self.static else ()
        return (DEADCAFE,)


class AxiCounter:
    """Counts the AXI handshakes of every port in HBM_CLK cycles and keeps the cycle of the first ones. A port has
    drained once each channel group was open, unpaused and without VALID, for `idle` cycles: HBM_TESTER shows
    AWVALID only with WREADY and WVALID only with AWREADY, and a paused memory channel hides pending beats."""

    def __init__(self, dut, ports, pauses):
        self.dut = dut
        self.ports = ports
        # (AW and W), B, AR, R of every port
        self.groups = [[(pz[0], pz[1]), (pz[2],), (pz[3],), (pz[4],)] for pz in pauses]
        self.sig = [{n: getattr(dut, f"P{p}_AXI_{n}") for n in (
            "AWVALID", "AWREADY", "WVALID", "WREADY", "BVALID", "BREADY", "ARVALID", "ARREADY", "RVALID", "RREADY")}
            for p in range(ports)]
        self.cycle = 0
        self.recording = False
        self.on_first_valid = None
        self.clear()
        cocotb.start_soon(self._run())

    @property
    def idle(self):
        return min(min(q) for q in self.quiet)

    def clear(self):
        self.w = [0] * self.ports
        self.r = [0] * self.ports
        self.r_cycles = [[] for _ in range(self.ports)]
        self.first = [dict() for _ in range(self.ports)]
        self.quiet = [[0] * 4 for _ in range(self.ports)]

    async def _run(self):
        edge = RisingEdge(self.dut.HBM_CLK)
        while True:
            await edge
            self.cycle += 1
            if not self.recording:
                continue
            for p, s in enumerate(self.sig):
                first = self.first[p]
                awv, arv = int(s["AWVALID"].value), int(s["ARVALID"].value)
                wv, rv, bv = int(s["WVALID"].value), int(s["RVALID"].value), int(s["BVALID"].value)
                if (awv or arv) and self.on_first_valid is not None:
                    self.on_first_valid()
                    self.on_first_valid = None
                if awv and "aw" not in first:
                    first["aw"] = self.cycle
                if arv and "ar" not in first:
                    first["ar"] = self.cycle
                if wv and int(s["WREADY"].value):
                    self.w[p] += 1
                if rv and int(s["RREADY"].value):
                    self.r[p] += 1
                    self.r_cycles[p].append(self.cycle)
                    first.setdefault("r", self.cycle)
                if bv and int(s["BREADY"].value):
                    first.setdefault("b", self.cycle)
                quiet = self.quiet[p]
                if awv | arv | wv | rv | bv:
                    quiet[:] = (0, 0, 0, 0)
                else:
                    for g, group in enumerate(self.groups[p]):
                        if not any(pz.paused for pz in group):
                            quiet[g] += 1


class AdcOrderCoverage:
    """Counts requests that reach HBM_TESTER_ADC in consecutive HBM_CLK cycles on one register: a read right after a
    write and a write right after a read."""

    def __init__(self, dut):
        self.adc = dut.hbm_tester_i.adc_i
        self.clk = dut.HBM_CLK
        self.raw = self.war = 0
        cocotb.start_soon(self._run())

    async def _run(self):
        prev = None
        adc = self.adc
        while True:
            await RisingEdge(self.clk)
            rd, wr = int(adc.MI_RD.value), int(adc.MI_WR.value)
            cur = (wr, int(adc.MI_ADDR.value) & 0xFFF) if (rd or wr) else None
            if cur and prev and cur[1] == prev[1]:
                self.raw += prev[0] and not cur[0]
                self.war += cur[0] and not prev[0]
            prev = cur


class HbmTesterBench:
    def __init__(self, dut):
        self.dut = dut
        self.log = dut._log
        self.rng = random.Random(cocotb.RANDOM_SEED)
        self.ports = int(dut.PORTS.value)
        self.cnt_width = int(dut.CNT_WIDTH.value)
        self.addr_width = len(dut.P0_AXI_AWADDR)
        self.data_width = len(dut.P0_AXI_WDATA)
        self.model = RegModel(self.ports, self.cnt_width)
        self.mi = MIPipelinedDriver(dut, "MI", dut.MI_CLK)
        self.mi_mon = MIMonitor(dut, "MI", dut.MI_CLK, callback=self._mi_seen)
        self.pending = deque()
        self.answers = deque()
        self.checked_reads = 0
        self.armed = False
        self.freeze = False
        self.run_id = 0
        self.pause_rate = 0.0
        self.readouts = []
        self.lat_offsets = {"rd": set(), "wr": set()}
        self.rd_offsets = set()

        self.rams = []
        pauses = []
        for p in range(self.ports):
            ram = AxiRam(AxiBus.from_prefix(dut, f"P{p}_AXI"), dut.HBM_CLK, dut.HBM_RESET, size=2**self.addr_width)
            ram.write_if.log.setLevel(logging.WARNING)
            ram.read_if.log.setLevel(logging.WARNING)
            pauses.append([])
            for ch in (ram.write_if.aw_channel, ram.write_if.w_channel, ram.write_if.b_channel,
                       ram.read_if.ar_channel, ram.read_if.r_channel):
                pauses[-1].append(ArmedPause(self))
                ch.set_pause_generator(pauses[-1][-1])
            self.rams.append(ram)
        self.axi = AxiCounter(dut, self.ports, pauses)
        self.order = AdcOrderCoverage(dut)

    # -------------------------------------------------------------------------
    #  MI access through the register model
    # -------------------------------------------------------------------------

    def _now_ps(self):
        return cocotb.utils.get_sim_time("ps")

    def _accepted(self, op):
        now = self._now_ps()
        if op.write:
            self.model.write(op.addr, op.data, now)
            op.done.set()
        else:
            op.expected = self.model.read(op.addr, now)
            self.pending.append(op)
            self._match()

    def _mi_seen(self, trans):
        # Before HBM_INIT_DONE the read data comes in the ARDY cycle, possibly ahead of the driver's own callback.
        if trans.trans_type == MiTransactionType.Request:
            self.answers.append(trans)
            self._match()

    def _match(self):
        while self.pending and self.answers:
            op, trans = self.pending.popleft(), self.answers.popleft()
            assert trans.addr == op.addr, f"MI read of 0x{op.addr:x} answered for 0x{trans.addr:x}"
            op.value = int.from_bytes(trans.data, "little")
            if op.expected:
                assert op.value in op.expected, (f"MI read 0x{op.addr:x}: 0x{op.value:08x}, expected "
                                                 f"{' or '.join(f'0x{v:08x}' for v in op.expected)}")
                self.checked_reads += 1
            op.done.set()

    async def issue(self, ops, gap=lambda: 0):
        await self.mi.issue(ops, self._accepted, gap)
        for op in ops:
            await op.done.wait()

    async def write(self, addr, data):
        await self.issue([MiOp(True, addr, data)])

    async def read(self, addr):
        op = MiOp(False, addr)
        await self.issue([op])
        return op.value

    # -------------------------------------------------------------------------
    #  Register map test
    # -------------------------------------------------------------------------

    def random_addr(self):
        """A register address; MI_ADDR(8 downto 4) stays below PORTS as HBM_TESTER indexes its counters with it."""
        rng = self.rng
        kind = rng.random()
        if kind < 0.45:
            reg = rng.choice((REG_VERSION, REG_RUN, REG_CONFIG, REG_MON_RESET, REG_TIME, REG_DONE, REG_TIME, REG_RUN))
        elif kind < 0.7:
            reg = REG_STAT + 0x10 * rng.randrange(self.ports) + rng.choice((0x0, 0x4, 0x8, 0xC))
        else:
            reg = (rng.randrange(8) << 9) | (rng.randrange(min(self.ports, 16)) << 4) | (rng.randrange(4) << 2)
        if rng.random() < 0.25:
            reg |= rng.getrandbits(20) << 12
        return reg

    def random_data(self, addr):
        rng = self.rng
        data = rng.getrandbits(32)
        reg = addr & 0xFFF
        if reg == REG_CONFIG:
            # No generator may reach the AXI side here, so DONE and the counters stay predictable.
            data &= ~CFG_CONNECT
        elif reg == REG_TIME and rng.random() < 0.3:
            data &= ~self.model.cnt_mask
        return data

    def random_sequence(self):
        """Random requests and read-after-write / write-after-read pairs on the same register."""
        rng, ops = self.rng, []
        for _ in range(rng.randint(1, 24)):
            addr = self.random_addr()
            kind = rng.random()
            if kind < 0.3:
                ops += [MiOp(True, addr, self.random_data(addr)), MiOp(False, addr)]
            elif kind < 0.5:
                ops += [MiOp(False, addr), MiOp(True, addr, self.random_data(addr)), MiOp(False, addr)]
            elif kind < 0.6:
                ops += [MiOp(True, addr, self.random_data(addr)), MiOp(True, addr, self.random_data(addr)),
                        MiOp(False, addr)]
            elif kind < 0.8:
                ops.append(MiOp(True, addr, self.random_data(addr)))
            else:
                ops.append(MiOp(False, addr))
        return ops

    def random_gap(self):
        return 0 if self.rng.random() < 0.7 else self.rng.randint(1, 6)

    async def register_phase(self, sequences):
        for _ in range(sequences):
            await self.issue(self.random_sequence(), self.random_gap)
            if self.rng.random() < 0.3:
                await ClockCycles(self.dut.MI_CLK, self.rng.randint(1, 50))

    # -------------------------------------------------------------------------
    #  Generator runs
    # -------------------------------------------------------------------------

    async def reset_monitors(self):
        mask = 2**self.ports - 1
        await self.write(REG_MON_RESET, mask)
        await self.write(REG_MON_RESET, 0)

    async def wait_done(self, timeout_cycles):
        mask = 2**self.ports - 1
        for _ in range(timeout_cycles // 100 + 1):
            if await self.read(REG_DONE) == mask:
                return
            await ClockCycles(self.dut.HBM_CLK, 100)
        raise AssertionError(f"DONE vector never reached 0x{mask:x}")

    async def read_counters(self):
        values = []
        for p in range(self.ports):
            values.append((await self.read(REG_STAT + 0x10 * p), await self.read(REG_STAT + 0x10 * p + 4)))
        return values

    def _arm(self):
        self.armed = True

    async def start_run(self, cfg, time, pause_rate):
        """Configures, resets the monitors and starts all generators; the AXI backpressure starts with their traffic."""
        await self.park_generators()
        self.run_id += 1
        # BackpressureGenerator draws from the global stream; reseeding it per run keeps every run reproducible.
        random.seed(self.rng.getrandbits(32))
        self.pause_rate = pause_rate
        self.armed = False
        self.axi.clear()
        self.axi.on_first_valid = self._arm
        self.axi.recording = True
        await self.write(REG_TIME, time)
        await self.write(REG_CONFIG, cfg)
        await self.reset_monitors()
        await self.write(REG_RUN, 2**self.ports - 1)

    async def stop_and_drain(self):
        await self.write(REG_RUN, 0)
        self.freeze = False
        for _ in range(20000):
            if self.axi.idle >= 32:
                break
            await RisingEdge(self.dut.HBM_CLK)
        else:
            busy = {f"P{p}_{n}": int(v.value) for p, sig in enumerate(self.axi.sig) for n, v in sig.items()}
            raise AssertionError(f"the AXI traffic did not drain: {busy}")
        self.axi.recording = False

    async def park_generators(self):
        """Stops a generator left running: its run flag clears only on a burst's last word, which a read-only BL8 run
        never reaches, and the next configuration with writes would otherwise start writing at once."""
        await self.write(REG_RUN, 0)
        await self.write(REG_CONFIG, config(RUN_RD, 0, 0))
        await ClockCycles(self.dut.HBM_CLK, 20)

    def record(self, kind, cfg, time, counters):
        self.readouts.append((kind, hex(cfg), time, counters))
        self.log.info(f"readout {kind} cfg 0x{cfg:x} TIME {time}: {counters}")

    def random_switch(self, run_mode):
        """The R/W switch alternates a write burst and a read, so with one direction only the generator stalls."""
        return self.rng.choice((0, CFG_RW_SWITCH)) if run_mode == RUN_RW else 0

    async def run_bounded(self, run_mode, cnt0, cnt1, flags):
        """The software flow: the window closes while the generators run, then the counters are read."""
        time = self.rng.randint(100, 1500)
        cfg = config(run_mode, cnt0, cnt1, flags)
        await self.start_run(cfg, time, self.rng.choice(PAUSE_RATES))
        await self.wait_done(time + 4000)
        counters = await self.read_counters()
        await self.stop_and_drain()
        self.record("bounded", cfg, time, counters)
        return time, counters

    async def run_full_window(self):
        """The window outlives the traffic: the backpressure stops all traffic after a random number of cycles, so the
        word counters must equal the AXI handshakes of the whole run."""
        rng = self.rng
        run_mode = rng.choice((RUN_WR, RUN_RD, RUN_RW))
        flags = rng.choice((0, CFG_RAND_ADDR)) | rng.choice((0, CFG_BL8)) | self.random_switch(run_mode)
        flags |= rng.choice((0, CFG_NO_WAIT)) | rng.choice((0, CFG_AXI_ID))
        cfg = config(run_mode, MODE_RD_WORDS, MODE_WR_WORDS, flags)
        cycles = rng.randint(300, 1500)
        pause_rate = rng.choice(PAUSE_RATES)
        # The drain runs at the AXI side's ready rate, so its margin before the window closes scales the same way.
        time = rng.randint(cycles + int(1500 / (1 - pause_rate)), 2**self.cnt_width - 1)
        await self.start_run(cfg, time, pause_rate)
        for _ in range(2000):
            if self.armed:
                break
            await RisingEdge(self.dut.HBM_CLK)
        else:
            raise AssertionError(f"no generator traffic started (cfg 0x{cfg:x})")
        await ClockCycles(self.dut.HBM_CLK, cycles)
        self.freeze = True
        await self.write(REG_RUN, 0)
        await ClockCycles(self.dut.HBM_CLK, 50)
        await self.stop_and_drain()
        mask = 2**self.ports - 1
        assert await self.read(REG_DONE) != mask, "the window closed before the traffic had drained"
        await self.wait_done(time + 4000)
        counters = await self.read_counters()
        self.record("full", cfg, time, counters)
        for p, (rd, wr) in enumerate(counters):
            assert (rd, wr) == (self.axi.r[p], self.axi.w[p]), (
                f"port {p}: read/write words {rd}/{wr}, the AXI side saw {self.axi.r[p]}/{self.axi.w[p]} (cfg 0x{cfg:x})")
            if run_mode & RUN_RD:
                assert rd > 0, f"port {p}: no read word in a run with reads"
            if run_mode & RUN_WR:
                assert wr > 0, f"port {p}: no write word in a run with writes"

    def check_rd_window(self, p, time, rd):
        """Read words in a window that closed during traffic: the read data PIPE never stalls, so they are the AXI R
        handshakes in TIME cycles at a fixed offset from the first AW, the same offset on every port and run."""
        start = self.axi.first[p]["aw"]
        cycles = self.axi.r_cycles[p]
        offsets = {k for k in range(MAX_PIPE_OFFSET + 1)
                   if sum(start - k <= c < start - k + time for c in cycles) == rd}
        assert offsets, f"port {p}: {rd} read words match no window of the AXI R handshakes"
        self.rd_offsets = offsets if not self.rd_offsets else self.rd_offsets & offsets
        assert self.rd_offsets, f"port {p}: the read windows need different pipe offsets"

    async def run_data(self):
        rng = self.rng
        flags = CFG_RW_SWITCH | rng.choice((0, CFG_BL8)) | rng.choice((0, CFG_AXI_ID))
        pair = rng.choice(((MODE_RD_WORDS, MODE_DATA_OK), (MODE_DATA_ERR, MODE_WR_WORDS)))
        time, counters = await self.run_bounded(RUN_RW, pair[0], pair[1], flags)
        for p, (c0, c1) in enumerate(counters):
            if pair[0] == MODE_RD_WORDS:
                assert c0 == c1, f"port {p}: {c0} read words but {c1} correct ones"
                assert 0 < c0 <= min(time, self.axi.r[p]), f"port {p}: {c0} read words, TIME {time}"
                self.check_rd_window(p, time, c0)
            else:
                assert c0 == 0, f"port {p}: {c0} read data errors"
                assert 0 < c1 <= min(time, self.axi.w[p]), f"port {p}: {c1} write words, TIME {time}"

    async def run_latency(self):
        """Latency counts from the first word of the window to its response; the HSI-to-AXI pipes add a constant."""
        rng = self.rng
        run_mode = rng.choice((RUN_RD, RUN_RW))
        flags = rng.choice((0, CFG_BL8)) | self.random_switch(run_mode) | rng.choice((0, CFG_AXI_ID))
        _, counters = await self.run_bounded(run_mode, MODE_RD_LAT, MODE_WR_LAT, flags)
        # Without the R/W switch the first write and the first read address start the window in the same cycle.
        both = run_mode == RUN_RW and not flags & CFG_RW_SWITCH
        for p, (rd_lat, wr_lat) in enumerate(counters):
            first = self.axi.first[p]
            checks = []
            if run_mode == RUN_RD or both:
                checks.append(("rd", rd_lat, first["r"] - first["ar"]))
            else:
                assert rd_lat == 0, f"port {p}: read latency {rd_lat} in a window opened by a write"
            if run_mode == RUN_RW:
                checks.append(("wr", wr_lat, first["b"] - first["aw"]))
            else:
                assert wr_lat == 0, f"port {p}: write latency {wr_lat} in a read-only run"
            for kind, lat, axi_lat in checks:
                offset = lat - axi_lat
                assert 0 <= offset <= MAX_PIPE_OFFSET, f"port {p}: {kind} latency {lat}, AXI side {axi_lat}"
                self.lat_offsets[kind].add(offset)
                assert len(self.lat_offsets[kind]) == 1, f"{kind} latency offsets differ: {self.lat_offsets[kind]}"


@cocotb.test()
async def run_random_test(dut):
    tb = HbmTesterBench(dut)
    rng = tb.rng
    # A faster MI_CLK queues requests in MI_ASYNC, so that they leave it back to back in HBM_CLK.
    mi_ps = rng.randrange(2001, 3901, 2) if rng.random() < 0.6 else rng.randrange(3901, 9001, 2)
    tb.log.info(f"PORTS {tb.ports}, data width {tb.data_width}, CNT_WIDTH {tb.cnt_width}, "
                f"HBM_CLK {HBM_CLK_PS} ps, MI_CLK {mi_ps} ps")

    dut.HBM_RESET.value = 1
    dut.MI_RESET.value = 1
    dut.HBM_INIT_DONE.value = 0
    cocotb.start_soon(Clock(dut.HBM_CLK, HBM_CLK_PS, unit="ps").start())
    await ClockCycles(dut.HBM_CLK, rng.randint(1, 3))
    cocotb.start_soon(Clock(dut.MI_CLK, mi_ps, period_high=mi_ps // 2, unit="ps").start())
    await ClockCycles(dut.MI_CLK, 10)
    dut.MI_RESET.value = 0
    await ClockCycles(dut.HBM_CLK, rng.randint(1, 20))
    dut.HBM_RESET.value = 0
    await ClockCycles(dut.HBM_CLK, 50)

    # Before HBM_INIT_DONE every read returns DEAD2BAD and every write is dropped.
    await tb.register_phase(10)
    await ClockCycles(dut.MI_CLK, 5)
    dut.HBM_INIT_DONE.value = 1
    await ClockCycles(dut.HBM_CLK, 5)
    await ClockCycles(dut.MI_CLK, 10)
    tb.model.init_done = True
    for reg, value in RESET_VALUES.items():
        assert await tb.read(reg) == value, f"register 0x{reg:x} lost its reset value to a write before HBM_INIT_DONE"

    await tb.register_phase(150)
    tb.log.info(f"register map: {tb.checked_reads} reads checked")

    tb.model.static = False
    for _ in range(4):
        await tb.run_full_window()
        await tb.run_data()
        await tb.run_latency()
    await tb.write(REG_CONFIG, 0)
    await tb.reset_monitors()
    # The cleared time counters reach the DONE register through the same register stages as a TIME write.
    await Timer(DONE_SETTLE_PS, unit="ps")
    tb.model.static = True
    await tb.register_phase(20)

    tb.log.info(f"summary: {tb.checked_reads} MI reads checked, back to back at the ADC: {tb.order.raw} reads after "
                f"writes, {tb.order.war} writes after reads, read window offsets {sorted(tb.rd_offsets)}, "
                f"latency offsets {tb.lat_offsets}, {len(tb.readouts)} runs")
    if mi_ps < HBM_CLK_PS:
        assert tb.order.raw > 0 and tb.order.war > 0, "no back-to-back read and write of a register reached the ADC"
