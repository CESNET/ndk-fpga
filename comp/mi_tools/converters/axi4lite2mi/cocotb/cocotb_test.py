# cocotb_test.py: Cocotb tests of the AXI4-Lite to MI converter
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2026
#
# SPDX-License-Identifier: BSD-3-Clause

"""Verification of AXI4LITE2MI.

The main test is one randomized test with concurrent reads and writes, run in
several backpressure scenarios. The remaining tests cover situations a random
run is not guaranteed to hit reliably, check the documented timing or are
regression tests of fixed bugs.
"""

import os
from typing import Any

import cocotb
from cocotb.triggers import ClockCycles, Combine, RisingEdge

from testbench import Testbench, get_testbench

# Number of AXI transactions of the randomized test, COCOTB_TRANSACTIONS is set by multi_ver.
TRANSACTIONS = int(os.environ.get("COCOTB_TRANSACTIONS", "2000"))

# Generous for the slowest scenario (about 0.06 us per transaction), short enough
# that a hung bus fails quickly.
TIMEOUT_US = 200 + TRANSACTIONS // 5

# (AXI master channel pauses aw, w, b, ar, r), (MI_ARDY stall rate, read latency min, max)
SCENARIOS = {
    "ideal"            : ((0.0, 0.0, 0.0, 0.0, 0.0), (0.0, 0, 0)),
    "axi_backpressure" : ((0.4, 0.4, 0.5, 0.4, 0.5), (0.0, 0, 0)),
    "mi_latency"       : ((0.0, 0.0, 0.0, 0.0, 0.0), (0.5, 0, 8)),
    "everything"       : ((0.3, 0.5, 0.3, 0.3, 0.3), (0.3, 0, 5)),
}


async def random_worker(tb: Testbench, write: bool, count: int, region_words: int) -> None:
    """Issues random single and multi-word, aligned and unaligned AXI accesses.

    Every tenth access goes anywhere in the address space to exercise the
    upper address bits and ADDR_MASK; the rest stay in a small region so that
    reads hit previously written words.
    """
    for _ in range(count):
        length = tb.rng.randint(1, 3 * tb.word_bytes)
        aligned = tb.rng.random() < 0.5
        region = None if tb.rng.random() < 0.1 else region_words
        addr = tb.random_address(length, region, aligned=aligned)

        if write:
            await tb.write(addr, tb.rng.randbytes(length))
        else:
            await tb.read(addr, length)

        if tb.rng.random() < 0.2:
            await ClockCycles(tb.dut.CLK, tb.rng.randint(1, 5))


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
@cocotb.parametrize(scenario=list(SCENARIOS))
async def test_random(dut: Any, scenario: str) -> None:
    """Concurrent random reads and writes from two writers and two readers.

    The cocotbext-axi master keeps several requests queued, so AR and AW
    requests regularly compete in the same cycle and the arbitration, the
    serialization and all channel handshakes are exercised together.
    """
    tb = await get_testbench(dut, seed=list(SCENARIOS).index(scenario) + 1)
    axi, mi = SCENARIOS[scenario]
    tb.set_axi_backpressure(*axi)
    tb.set_mi(*mi)

    per_worker = max(1, TRANSACTIONS // 4)
    workers = [cocotb.start_soon(random_worker(tb, write, per_worker, region_words=16))
               for write in (True, True, False, False)]
    await Combine(*workers)

    await tb.drain()
    tb.check()


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_write_read_back(dut: Any, count: int = 300) -> None:
    """Writes followed by reads of the same bytes, compared end to end.

    Partial and unaligned writes have to merge correctly with the data already
    in the MI memory, which is only visible when the bytes are read back.
    """
    tb = await get_testbench(dut, seed=11)
    tb.set_axi_backpressure(0.2, 0.2, 0.2, 0.2, 0.2)
    tb.set_mi(0.2, 0, 3)

    for _ in range(count):
        length = tb.rng.randint(1, 2 * tb.word_bytes)
        addr = tb.random_address(length, region_words=8)
        await tb.write(addr, tb.rng.randbytes(length))
        read_addr = tb.random_address(length, region_words=8)
        await tb.read_check(read_addr, length)

    await tb.drain()
    tb.check()


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_read_has_priority(dut: Any, count: int = 50) -> None:
    """AR and AW presented in the same cycle: the read must be served first."""
    tb = await get_testbench(dut, seed=12)
    both_valid = 0

    for i in range(count):
        tb.set_mi(0.0, i % 3, i % 3)
        tb.mi.clear()
        tb.checker.clear()

        read = tb.axi.init_read(4 * (i % 8), 4)
        write = tb.axi.init_write(4 * (i % 8), tb.rng.randbytes(4))

        await RisingEdge(dut.CLK)
        while not (dut.AXI_ARVALID.value and dut.AXI_AWVALID.value):
            await RisingEdge(dut.CLK)
        both_valid += 1

        await Combine(read.wait(), write.wait())
        await tb.drain(2)

        assert tb.checker.ar[0].cycle < tb.checker.aw[0].cycle, "write address accepted before the read address"
        assert tb.checker.r[0].cycle < tb.checker.aw[0].cycle, "write address accepted before the read completed"
        kinds = ["WR" if r.write else "RD" for r in tb.mi.requests]
        assert kinds == ["RD", "WR"], f"MI request order {kinds}, expected the read first"
        tb.check()

    assert both_valid == count


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
@cocotb.parametrize(order=["data_first", "together", "address_first"])
async def test_write_channel_order(dut: Any, order: str, delay: int = 6) -> None:
    """Write data presented before, together with, or after the write address.

    The DUT asserts WREADY only after the address handshake, so data presented
    first has to wait with WVALID high.
    """
    tb = await get_testbench(dut, seed=13)
    aw = tb.axi.write_if.aw_channel
    w = tb.axi.write_if.w_channel

    for i in range(8):
        addr = 4 * i
        data = tb.rng.randbytes(4)

        aw.pause = order == "data_first"
        w.pause = order == "address_first"
        done = tb.axi.init_write(addr, data)

        if order != "together":
            await ClockCycles(dut.CLK, delay)
            if order == "data_first":
                assert dut.AXI_WVALID.value == 1 and dut.AXI_AWVALID.value == 0
                assert dut.AXI_WREADY.value == 0, "WREADY asserted without a write address"
            else:
                assert dut.AXI_AWVALID.value == 0 and dut.AXI_WVALID.value == 0, "AW handshake expected already"
                assert len(tb.checker.aw) == i + 1 and len(tb.checker.w) == i
            aw.pause = False
            w.pause = False

        await done.wait()
        tb.note_write(addr, data)
        await tb.read_check(addr, 4)

    await tb.drain()
    tb.check()


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
@cocotb.parametrize(latency=[0, 1, 2, 7, 50])
async def test_mi_read_latency(dut: Any, latency: int, count: int = 20) -> None:
    """Fixed MI read latency, including MI_DRDY in the same cycle as MI_ARDY.

    Latency 0 takes the ST_READ -> ST_READ_RESP path, the others go through
    ST_READ_ARDY; the counter of same-cycle answers proves which one was taken.
    """
    tb = await get_testbench(dut, seed=14)
    tb.set_mi(0.0, latency, latency)

    for _ in range(count):
        addr = tb.random_address(4, region_words=16, aligned=True)
        await tb.write(addr, tb.rng.randbytes(4))
        await tb.read_check(addr, 4)
        await tb.read_check(tb.random_address(4, region_words=16, aligned=True), 4)

    await tb.drain()
    tb.check()

    if latency == 0:
        assert tb.mi.same_cycle_responses == 2 * count, f"{tb.mi.same_cycle_responses} same-cycle responses"
    else:
        assert tb.mi.same_cycle_responses == 0


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_mi_ardy_stall(dut: Any, stall: int = 40) -> None:
    """The MI slave keeps MI_ARDY low for a long time; the request must stay stable."""
    tb = await get_testbench(dut, seed=15)

    for write in (True, False, True, False):
        tb.mi.set_ready(iter([False] * stall + [True] * 1000000))
        addr = tb.random_address(4, region_words=16, aligned=True)
        if write:
            await tb.write(addr, tb.rng.randbytes(4))
        else:
            await tb.read_check(addr, 4)

    await tb.drain()
    tb.check()


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_response_backpressure(dut: Any, hold: int = 25) -> None:
    """RREADY and BREADY held low: the response must stay valid and stable and
    no new request may be accepted in the meantime."""
    tb = await get_testbench(dut, seed=16)
    r = tb.axi.read_if.r_channel
    b = tb.axi.write_if.b_channel

    for channel, first_is_read in ((r, True), (b, False)):
        accepted = len(tb.checker.aw) + len(tb.checker.ar)
        channel.pause = True
        first = tb.axi.init_read(0x10, 4) if first_is_read else tb.axi.init_write(0x10, tb.rng.randbytes(4))
        await ClockCycles(dut.CLK, 6)
        other = tb.axi.init_write(0x14, tb.rng.randbytes(4)) if first_is_read else tb.axi.init_read(0x14, 4)
        await ClockCycles(dut.CLK, hold)

        valid = dut.AXI_RVALID if first_is_read else dut.AXI_BVALID
        assert valid.value == 1, "response not presented"
        assert len(tb.checker.aw) + len(tb.checker.ar) == accepted + 1, "second request accepted while the response is pending"

        channel.pause = False
        await Combine(first.wait(), other.wait())

    await tb.drain()
    tb.check()


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_timing(dut: Any, count: int = 16) -> None:
    """Latency and throughput documented in readme.rst, with an ideal master and slave.

    RVALID comes 2 cycles after the AR handshake and BVALID 3 cycles after the
    AW handshake; back-to-back accesses are accepted every 3 (read) or 4
    (write) cycles.
    """
    tb = await get_testbench(dut, seed=17)
    tb.set_mi(0.0, 0, 0)

    await Combine(*[tb.axi.init_read(4 * i, 4).wait() for i in range(count)])
    await tb.drain(2)
    ar, rr = tb.checker.ar, tb.checker.r
    assert all(r.cycle - a.cycle == 2 for a, r in zip(ar, rr)), [r.cycle - a.cycle for a, r in zip(ar, rr)]
    assert all(b.cycle - a.cycle == 3 for a, b in zip(ar, ar[1:])), [b.cycle - a.cycle for a, b in zip(ar, ar[1:])]
    tb.check()

    tb.checker.clear()
    tb.mi.clear()
    await Combine(*[tb.axi.init_write(4 * i, tb.rng.randbytes(4)).wait() for i in range(count)])
    await tb.drain(2)
    aw, bb = tb.checker.aw, tb.checker.b
    assert all(b.cycle - a.cycle == 3 for a, b in zip(aw, bb)), [b.cycle - a.cycle for a, b in zip(aw, bb)]
    assert all(b.cycle - a.cycle == 4 for a, b in zip(aw, aw[1:])), [b.cycle - a.cycle for a, b in zip(aw, aw[1:])]
    tb.check()


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_read_byte_enable(dut: Any) -> None:
    """Regression: MI_BE must be all ones for every MI read.

    MI_BE used to carry the strobes of the last write (and was undefined
    before the first write). The MI slave model flags any other value.
    """
    tb = await get_testbench(dut, seed=18)

    await tb.read_check(0x0, 4)  # first access after reset
    for strobe_bytes in ((1, b"\xaa"), (2, b"\xbb\xcc")):
        offset, data = strobe_bytes
        await tb.write(0x8 + offset, data)
        await tb.read_check(0x8, 4)

    await tb.drain()
    tb.check()


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_address_range(dut: Any) -> None:
    """Lowest and highest addresses, all address bits toggled; MI_ADDR = address and ADDR_MASK."""
    tb = await get_testbench(dut, seed=19)
    top = 2**tb.addr_width
    patterns = [0, 4, top - 4, top - 1, top // 2, (top - 1) & 0x5555_5555, (top - 1) & 0xAAAA_AAAA,
                top - 8 + 1, 0x8000_0000 % top]

    for addr in patterns:
        length = min(4, top - addr)
        await tb.write(addr, tb.rng.randbytes(length))
        await tb.read_check(addr, length)

    await tb.drain()
    tb.check()


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_reset_during_traffic(dut: Any, rounds: int = 8) -> None:
    """Reset asserted at random points of ongoing traffic.

    After every reset the DUT has to be idle and work normally; the master and
    the MI slave are reset together with it, as they would be in a design.
    """
    tb = await get_testbench(dut, seed=20)
    tb.set_axi_backpressure(0.3, 0.3, 0.3, 0.3, 0.3)
    tb.set_mi(0.3, 0, 4)

    for _ in range(rounds):
        for _ in range(6):
            addr = tb.random_address(4, region_words=16, aligned=True)
            if tb.rng.random() < 0.5:
                tb.axi.init_write(addr, tb.rng.randbytes(4))
            else:
                tb.axi.init_read(addr, 4)

        await ClockCycles(dut.CLK, tb.rng.randint(1, 25))
        await tb.reset(cycles=tb.rng.randint(1, 3))

        assert dut.AXI_RVALID.value == 0 and dut.AXI_BVALID.value == 0
        assert dut.MI_RD.value == 0 and dut.MI_WR.value == 0

        for _ in range(4):
            addr = tb.random_address(4, region_words=16, aligned=True)
            await tb.write(addr, tb.rng.randbytes(4))
            await tb.read_check(addr, 4)

        await tb.drain()
        tb.check()


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
async def test_idle(dut: Any, cycles: int = 200) -> None:
    """Without AXI requests the DUT must not issue any MI request or AXI response."""
    tb = await get_testbench(dut, seed=21)
    tb.set_mi(0.5, 0, 3)

    await ClockCycles(dut.CLK, cycles)

    assert not tb.mi.requests, f"MI requests without AXI traffic: {tb.mi.requests}"
    tb.check()
