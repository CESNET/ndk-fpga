# testbench.py: Testbench infrastructure of the AXI-AVMM interface bridge unit
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author: David Beneš <benes@dyna-nic.com>, 2026
#
# SPDX-License-Identifier: BSD-3-Clause

"""Testbench infrastructure for the Avalon-MM to AXI4 DDR bridge.

The Avalon-MM side is driven by the shared NDK master driver, the AXI side is
terminated by a cocotbext-axi slave memory. Two independent observers watch the
bridge: a monitor of the Avalon-MM requests and an AXI protocol checker.
"""

import random
from typing import Any, Iterator, Optional

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, RisingEdge
from cocotbext.axi import AxiBus, AxiRam
from cocotbext.ofm.avmm.config import AvalonMMDataUnits, AvalonMMParams
from cocotbext.ofm.avmm.drivers import AvalonMMDriverMaster

from axi_checker import AxiProtocolChecker
from model import MemoryModel
from monitor import AmmMonitor
from scoreboard import Scoreboard

# The bridge does not use the plain Avalon-MM port names.
AMM_SIGNAL_MAP = {
    "address"       : "ADDRESS",
    "burstcount"    : "BURST_COUNT",
    "write"         : "WRITE",
    "writedata"     : "WRITE_DATA",
    "read"          : "READ",
    "ready"         : "READY",
    "readdata"      : "READ_DATA",
    "readdatavalid" : "READ_DATA_VALID",
}

CLK_PERIOD_NS = 4


def random_pauses(rate: float, seed: int) -> Iterator[bool]:
    """Pause pattern for an AXI channel; rate is the fraction of stalled cycles."""
    rng = random.Random(seed)

    while True:
        yield rng.random() < rate


class AxiRamSlave(AxiRam):
    """Sparse AXI4 slave memory whose only backpressure comes from set_backpressure().

    cocotbext-axi queues just two requests per channel and stalls the handshake
    once that many are pending, which would mix its own throttling into every
    measurement. Deep queues leave the pauses entirely to the test.
    """

    def __init__(self, bus: Any, clock: Any, reset: Any = None, size: int = 2**32) -> None:
        super().__init__(bus, clock, reset, size=size)

        for channel in (self.write_if.aw_channel, self.write_if.w_channel, self.write_if.b_channel,
                        self.read_if.ar_channel, self.read_if.r_channel):
            channel.queue_occupancy_limit = 4096


class Testbench:
    def __init__(self, dut: Any, constant_burst: bool = True) -> None:
        self.dut = dut

        self.log = cocotb.log
        self.word_bytes = len(dut.AMM_WRITE_DATA) // 8
        self.max_burst = 2 ** len(dut.AMM_BURST_COUNT) - 1

        # Avalon-MM defines address and burstcount only on the first beat; the NDK
        # masters hold them anyway, and constant_burst switches between the two.
        params = AvalonMMParams(
            addressUnits=AvalonMMDataUnits.words,
            constantBurstBehavior=constant_burst,
            maximumPendingReadTransactions=64,
        )

        self.master = AvalonMMDriverMaster(dut, "AMM", dut.MEM_CLK, params=params, signal_map=AMM_SIGNAL_MAP)
        self.ram = AxiRamSlave(AxiBus.from_prefix(dut, "DDR_S_AXI"), dut.MEM_CLK, dut.MEM_RST)

        self.model = MemoryModel(self.word_bytes)
        self.monitor = AmmMonitor(dut, dut.MEM_CLK, dut.MEM_RST, self.word_bytes, self.model)
        self.checker = AxiProtocolChecker(dut, dut.MEM_CLK, len(dut.DDR_S_AXI_WDATA))
        self.scoreboard = Scoreboard()

    def start_clock(self) -> None:
        cocotb.start_soon(Clock(self.dut.MEM_CLK, CLK_PERIOD_NS, unit="ns").start())

    async def reset(self) -> None:
        """Resets the DUT and drops all state collected by the previous test."""
        self.monitor.enable(False)
        self.checker.enable(False)

        self.dut.MEM_RST.value = 1
        await ClockCycles(self.dut.MEM_CLK, 10)
        self.dut.MEM_RST.value = 0
        await ClockCycles(self.dut.MEM_CLK, 5)

        self.monitor.enable(True)
        self.checker.enable(True)

    def set_backpressure(self, aw: float = 0.0, w: float = 0.0, b: float = 0.0,
                         ar: float = 0.0, r: float = 0.0, seed: int = 0) -> None:
        """Sets the fraction of cycles each AXI channel stalls."""
        channels = (
            (self.ram.write_if.aw_channel, aw),
            (self.ram.write_if.w_channel, w),
            (self.ram.write_if.b_channel, b),
            (self.ram.read_if.ar_channel, ar),
            (self.ram.read_if.r_channel, r),
        )

        for index, (channel, rate) in enumerate(channels):
            if rate > 0.0:
                channel.set_pause_generator(random_pauses(rate, seed + index))
            else:
                channel.clear_pause_generator()

    def burst_limit(self, word_address: int) -> int:
        """Longest burst the AXI slave model accepts starting at this address.

        cocotbext-axi asserts on a burst that crosses a 4 KB boundary. It is a
        limit of the model, not a rule this testbench checks.
        """
        words_per_4k = 4096 // self.word_bytes
        return min(self.max_burst, words_per_4k - word_address % words_per_4k)

    def fill_memory(self, word_address: int, words: list[bytes]) -> None:
        """Backdoor fill of the AXI memory and of the reference model."""
        for offset, data in enumerate(words):
            address = word_address + offset
            self.ram.write(self.model.byte_address(address), data)
            self.model.write(address, data)

    def random_words(self, count: int, rng: random.Random) -> list[bytes]:
        return [rng.randbytes(self.word_bytes) for _ in range(count)]

    async def write(self, word_address: int, words: list[bytes],
                    burst_count: Optional[int] = None) -> None:
        """Writes words and records the intent in the reference model.

        burst_count defaults to one burst covering every word; a smaller value
        splits them into that many back-to-back bursts in one request.
        """
        for offset, data in enumerate(words):
            self.model.write(word_address + offset, data)

        await self.master.write(word_address, b"".join(words),
                                burst_count=burst_count or len(words))

    async def read(self, word_address: int, burst_count: int = 1) -> bytes:
        response = await self.master.read(word_address, burst_count=burst_count)
        return response.data

    async def stall_write_address(self, cycles: int) -> None:
        """Holds AWREADY low for a fixed number of cycles, then releases it."""
        self.ram.write_if.aw_channel.pause = True
        await ClockCycles(self.dut.MEM_CLK, cycles)
        self.ram.write_if.aw_channel.pause = False

    async def idle(self, cycles: int = 20) -> None:
        await ClockCycles(self.dut.MEM_CLK, cycles)

    def check(self) -> None:
        """Raises with a full report if any observer or comparison found a problem.

        Both paths are always compared, including the one a test does not
        exercise: an empty expectation is what catches traffic the bridge
        produced on its own, such as a write burst emitted for a read request.
        """
        self.checker.finish()

        self.scoreboard.check_write_path(self.monitor.write_beats, self.checker.write_beats)
        self.scoreboard.check_read_path(self.monitor.expected_read_words, self.monitor.expected_read_data, self.monitor.read_data)

        self.scoreboard.report(self.checker.summary(), self.checker.violation_count)


async def get_testbench(dut: Any, constant_burst: bool = True) -> Testbench:
    """Builds a testbench for one test and resets the DUT.

    Every test gets its own instance: cocotb cancels the tasks a test started
    once it ends, so the clock, the drivers and the observers of a shared
    testbench would be dead from the second test on.
    """
    dut.AMM_WRITE.value = 0
    dut.AMM_READ.value = 0
    dut.MEM_RST.value = 1

    testbench = Testbench(dut, constant_burst=constant_burst)
    testbench.start_clock()
    await RisingEdge(dut.MEM_CLK)

    await testbench.reset()
    return testbench
