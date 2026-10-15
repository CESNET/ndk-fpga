# testbench.py: Testbench infrastructure of the AXI4LITE2MI verification
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2026
#
# SPDX-License-Identifier: BSD-3-Clause

"""Testbench for the AXI4-Lite to MI converter.

The AXI4-Lite slave port is driven by the cocotbext-axi master, the MI master
port is terminated by a memory model. Two independent observers check the DUT:
an AXI4-Lite checker on the slave port and the MI slave itself on the master
port. The scoreboard compares the traffic of both ports at the end of a test.
"""

import logging
import random
import warnings
from typing import Any, Iterator, Optional

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, RisingEdge
from cocotbext.axi import AxiLiteBus, AxiLiteMaster, AxiResp

from axil_checker import AxiLiteSlaveChecker
from mi_slave import MiSlave
from model import Model, observed
from scoreboard import Scoreboard

# cocotbext-axi 0.1.28 still uses APIs that cocotb 2.0 deprecates (Event.data,
# Task.kill(), Edge triggers, ...); the warnings would be printed for every
# transaction and are not actionable here.
warnings.filterwarnings("ignore", category=DeprecationWarning, module=r"cocotbext\.axi")

CLK_PERIOD_NS = 4


def random_pauses(rate: float, seed: float) -> Iterator[bool]:
    """Pause pattern for a cocotbext-axi channel; rate is the fraction of paused cycles."""
    rng = random.Random(seed)

    while True:
        yield rng.random() < rate


class Testbench:
    def __init__(self, dut: Any, seed: int = 0, debug: bool = False) -> None:
        self.dut = dut
        self.log = cocotb.log
        self.rng = random.Random(seed)

        self.addr_width = len(dut.AXI_AWADDR)
        self.word_bytes = len(dut.AXI_WDATA) // 8
        self.addr_mask = self._addr_mask()

        # cocotbext-axi logs every transaction and channel reset at INFO level.
        logging.getLogger(f"cocotb.{dut._name}.AXI").setLevel(logging.DEBUG if debug else logging.WARNING)

        self.axi = AxiLiteMaster(AxiLiteBus.from_prefix(dut, "AXI"), dut.CLK, dut.RESET)
        self.mi = MiSlave(dut, dut.CLK, dut.RESET, random.Random(self.rng.random()))
        self.checker = AxiLiteSlaveChecker(dut, dut.CLK)
        self.model = Model(self.addr_mask, self.word_bytes)

        # Byte-level content as seen by the AXI master, valid for tests that
        # wait for each transaction before issuing the next one.
        self.shadow: dict[int, int] = {}

    def _addr_mask(self) -> int:
        all_ones = 2**self.addr_width - 1

        # GHDL (4.1) aborts with an internal VPI error on reading a vector generic.
        if "ghdl" in (cocotb.SIM_NAME or "").lower():
            self.log.warning("ADDR_MASK generic cannot be read in GHDL, assuming the default (all ones)")
            return all_ones

        try:
            return self.dut.ADDR_MASK.value.to_unsigned() & all_ones
        except AttributeError:
            self.log.warning("ADDR_MASK generic is not accessible, assuming the default (all ones)")
            return all_ones

    # ------------------------------------------------------------------ control

    def start_clock(self) -> None:
        cocotb.start_soon(Clock(self.dut.CLK, CLK_PERIOD_NS, unit="ns").start())

    async def reset(self, cycles: int = 5) -> None:
        """Resets the DUT and drops all traffic recorded so far."""
        self.checker.enable(False)
        self.mi.checking = False

        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, cycles)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)

        self.mi.clear()
        self.shadow.clear()
        self.checker.enable(True)
        self.mi.checking = True
        await ClockCycles(self.dut.CLK, 2)

    def set_axi_backpressure(self, aw: float = 0.0, w: float = 0.0, b: float = 0.0,
                             ar: float = 0.0, r: float = 0.0) -> None:
        """Fraction of cycles each channel of the master stalls.

        On AW, W and AR it delays VALID, on B and R it holds READY low.
        """
        channels = (
            (self.axi.write_if.aw_channel, aw),
            (self.axi.write_if.w_channel, w),
            (self.axi.write_if.b_channel, b),
            (self.axi.read_if.ar_channel, ar),
            (self.axi.read_if.r_channel, r),
        )

        for channel, rate in channels:
            if rate > 0.0:
                channel.set_pause_generator(random_pauses(rate, self.rng.random()))
            else:
                channel.clear_pause_generator()
                channel.pause = False

    def set_mi(self, ardy_stall: float = 0.0, latency_min: int = 0, latency_max: int = 0) -> None:
        """MI slave behaviour: fraction of cycles without MI_ARDY and the read latency range."""
        self.mi.set_ready_rate(ardy_stall)
        self.mi.set_latency(latency_min, latency_max)

    # ------------------------------------------------------------------ traffic

    def random_address(self, length: int, region_words: Optional[int] = 64, aligned: bool = False) -> int:
        """Random byte address; region_words limits it to the start of the address space, None to all of it."""
        top = 2**self.addr_width if region_words is None else min(2**self.addr_width, region_words * self.word_bytes)
        addr = self.rng.randrange(0, top - length + 1)
        return addr - addr % self.word_bytes if aligned else addr

    def note_write(self, addr: int, data: bytes) -> None:
        """Records a completed write in the shadow memory, at the address the MI side sees."""
        for offset, byte in enumerate(data):
            self.shadow[(addr + offset) & self.addr_mask] = byte

    async def write(self, addr: int, data: bytes) -> None:
        response = await self.axi.write(addr, data)
        assert response.resp == AxiResp.OKAY, f"write 0x{addr:x}: response {response.resp}"
        self.note_write(addr, data)

    async def read(self, addr: int, length: int) -> bytes:
        response = await self.axi.read(addr, length)
        assert response.resp == AxiResp.OKAY, f"read 0x{addr:x}: response {response.resp}"
        return response.data

    def expected_bytes(self, addr: int, length: int) -> bytes:
        """Content of a byte range as the shadow memory and the initial MI memory define it."""
        out = bytearray()
        for offset in range(length):
            byte_addr = (addr + offset) & self.addr_mask
            if byte_addr in self.shadow:
                out.append(self.shadow[byte_addr])
            else:
                word = self.mi.read_word(byte_addr // self.word_bytes)
                out.append(word[byte_addr % self.word_bytes])
        return bytes(out)

    async def read_check(self, addr: int, length: int) -> None:
        """Reads through the DUT and compares with the shadow memory (sequential tests only)."""
        data = await self.read(addr, length)
        expected = self.expected_bytes(addr, length)
        assert data == expected, f"read 0x{addr:x}+{length}: got {data.hex()}, expected {expected.hex()}"

    async def drain(self, cycles: int = 10) -> None:
        """Waits until the master has nothing in flight and the MI slave has answered everything."""
        await self.axi.wait()
        while self.mi.busy:
            await RisingEdge(self.dut.CLK)
        await ClockCycles(self.dut.CLK, cycles)

    # ------------------------------------------------------------------ checks

    def check(self) -> Scoreboard:
        """Compares both ports and raises with a full report on any problem."""
        self.checker.finish()

        sb = Scoreboard()
        exp_writes = self.model.expected_writes(self.checker.aw, self.checker.w)
        exp_reads = self.model.expected_reads(self.checker.ar)

        mi_writes = [observed(r) for r in self.mi.requests if r.write]
        mi_reads = [observed(r) for r in self.mi.requests if not r.write]

        if len(self.checker.aw) != len(self.checker.w):
            sb.errors.append(f"{len(self.checker.aw)} write address handshakes, {len(self.checker.w)} write data handshakes")

        sb.compare_lists("MI writes", exp_writes, mi_writes)
        sb.compare_lists("MI reads", exp_reads, mi_reads)
        sb.compare_lists("AXI read data (RDATA vs MI_DRD)",
                         [f"0x{int.from_bytes(d, 'little'):08x}" for d in self.mi.read_data],
                         [f"0x{h.data:08x}" for h in self.checker.r])
        sb.compare_lists("AXI read responses", [AxiResp.OKAY.value] * len(self.checker.ar), [h.resp for h in self.checker.r])
        sb.compare_lists("AXI write responses", [AxiResp.OKAY.value] * len(self.checker.aw), [h.resp for h in self.checker.b])
        sb.compare_memory(self.model.expected_memory(exp_writes, self.mi.baseline, self.mi.read_word), self.mi.memory, self.word_bytes)

        sb.add_errors("AXI4-Lite protocol", self.checker.violations, self.checker.violation_count)
        sb.add_errors("MI protocol", self.mi.violations)

        self.log.info("Checked %d MI writes, %d MI reads, %d read responses (%d answered in the MI_ARDY cycle)",
                      len(mi_writes), len(mi_reads), len(self.checker.r), self.mi.same_cycle_responses)
        sb.result()
        return sb


async def get_testbench(dut: Any, seed: int = 0, debug: bool = False) -> Testbench:
    """Builds a testbench for one test and resets the DUT.

    Every test gets its own instance: cocotb kills the tasks a test started when
    it ends, so the clock and the models of a shared testbench would be dead.
    """
    dut.RESET.value = 1
    dut.AXI_AWVALID.value = 0
    dut.AXI_WVALID.value = 0
    dut.AXI_ARVALID.value = 0
    dut.AXI_BREADY.value = 0
    dut.AXI_RREADY.value = 0

    tb = Testbench(dut, seed=seed, debug=debug)
    tb.start_clock()
    await RisingEdge(dut.CLK)
    await tb.reset()
    return tb
