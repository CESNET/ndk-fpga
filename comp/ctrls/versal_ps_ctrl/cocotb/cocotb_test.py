# cocotb_test.py: Cocotb tests of the Versal PS controller
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2026
#
# SPDX-License-Identifier: BSD-3-Clause

"""Verification of VERSAL_PS_CTRL.

The main test is one randomized test in which the host software (MI) and the
BMC firmware (AXI4-Lite) work concurrently, run in several scenarios of PS
timing, error responses and clock ratios. The remaining tests check the
documented behaviour that a random run does not hit reliably: the FPGA ID
sequence and its resets, the window address translation, BUSY, the BMC
mailbox including simultaneous writes, and the recovery from AXI_LITE_RESET.
"""

import os
from typing import Any

import cocotb
from cocotb.triggers import ClockCycles, Combine, RisingEdge

from model import (BMC_MI_OFFSET, BMC_PS_OFFSET, BMC_REGS, BMC_WRITE_PRIORITY, DNA_BASE, LOWER_ADDR, STATUS,
                   STATUS_BUSY, UPPER_ADDR, WINDOW, WINDOW_SIZE, fpga_id_from_words)
from ps_axi_slave import DECERR, OKAY, SLVERR
from testbench import Testbench, get_testbench

# Number of host operations of the randomized test, COCOTB_TRANSACTIONS is set by multi_ver.
TRANSACTIONS = int(os.environ.get("COCOTB_TRANSACTIONS", "1500"))
TIMEOUT_US = 300 + TRANSACTIONS // 2

# Periods of CLK and AXI_LITE_CLK in ps
CLOCKS = {
    "axil_slower": (5000, 8000),
    "axil_faster": (8000, 3000),
    "same_period": (4000, 4000),
}

# (clocks, AW/W/AR ready rate, response latency min/max, error response rate)
SCENARIOS = {
    "ideal"        : ("axil_slower", 1.0, (0, 0), 0.0),
    "backpressure" : ("axil_faster", 0.3, (0, 2), 0.0),
    "slow_ps"      : ("same_period", 0.8, (5, 40), 0.0),
    "errors"       : ("axil_slower", 0.7, (0, 5), 0.3),
    "everything"   : ("axil_faster", 0.4, (0, 20), 0.2),
}


def scenario_seed(name: str, table: dict[str, Any]) -> int:
    return list(table).index(name) + 1


def random_resp(tb: Testbench, rate: float) -> None:
    if rate > 0.0:
        tb.slave.resp_fn = lambda write, addr: tb.slave.rng.choice((SLVERR, DECERR)) if tb.slave.rng.random() < rate else OKAY


async def host_worker(tb: Testbench, count: int) -> None:
    """Driver software: window accesses, window moves, register and STATUS accesses.

    Most window accesses go to a few words, so reads regularly return data
    written by the test, the rest anywhere in the window.
    """
    rng = tb.rng
    hot = [rng.randrange(0, WINDOW_SIZE, 4) for _ in range(8)] + [0x000, WINDOW_SIZE - 4]

    for _ in range(count):
        kind = rng.random()
        offset = rng.choice(hot) if rng.random() < 0.7 else rng.randrange(0, WINDOW_SIZE, 4)

        if kind < 0.40:
            await tb.window_write(offset, rng.getrandbits(32), rng.getrandbits(4))
        elif kind < 0.70:
            await tb.window_read(offset)
        elif kind < 0.75:
            await tb.set_window(rng.getrandbits(32), rng.getrandbits(32))
        elif kind < 0.85:
            await tb.status()
        elif kind < 0.92:
            reg = BMC_MI_OFFSET[rng.choice(BMC_REGS)]
            if rng.random() < 0.5:
                await tb.host_write(reg, rng.getrandbits(32), rng.getrandbits(4))
            else:
                await tb.host_read(reg)
        else:
            reg = rng.choice([UPPER_ADDR, LOWER_ADDR, rng.randrange(0x01C, WINDOW, 4)])
            if reg not in (UPPER_ADDR, LOWER_ADDR) and rng.random() < 0.5:
                await tb.host_write(reg, rng.getrandbits(32))
            else:
                await tb.host_read(reg)

        if rng.random() < 0.2:
            await ClockCycles(tb.dut.CLK, rng.randint(1, 10))


async def ps_worker(tb: Testbench, count: int) -> None:
    """BMC firmware: mailbox accesses through any alias, unmapped offsets and partial writes.

    All addresses are word aligned: AXI4LITE2MI passes the AXI address to the
    register block unchanged and the registers decode all 11 bits.
    """
    rng = tb.rng

    for _ in range(count):
        alias = rng.getrandbits(21) << 11
        if rng.random() < 0.8:
            offset = alias | BMC_PS_OFFSET[rng.choice(BMC_REGS)]
        else:
            offset = alias | rng.randrange(0x010, 0x800, 4)

        if rng.random() < 0.5:
            if rng.random() < 0.2:
                await tb.ps_write(offset, rng.getrandbits(32), rng.choice((1, 2, 3)))
            else:
                await tb.ps_write(offset, rng.getrandbits(32))
        else:
            await tb.ps_read(offset)

        if rng.random() < 0.3:
            await ClockCycles(tb.dut.AXI_LITE_CLK, rng.randint(1, 20))


@cocotb.test(timeout_time=TIMEOUT_US, timeout_unit="us")
@cocotb.parametrize(scenario=list(SCENARIOS))
async def test_random(dut: Any, scenario: str) -> None:
    """Host and BMC firmware traffic at the same time, with the PS timing of the scenario."""
    clocks, ready, latency, errors = SCENARIOS[scenario]
    tb = await get_testbench(dut, seed=scenario_seed(scenario, SCENARIOS), clk_ps=CLOCKS[clocks][0],
                             axil_ps=CLOCKS[clocks][1])
    tb.slave.set_ready_rates(ready, ready, ready)
    tb.slave.set_latency(*latency)
    random_resp(tb, errors)

    await tb.set_window(tb.rng.getrandbits(32), tb.rng.getrandbits(32))
    await Combine(cocotb.start_soon(host_worker(tb, TRANSACTIONS)),
                  cocotb.start_soon(ps_worker(tb, TRANSACTIONS // 2)))
    await tb.drain()
    tb.check()
    tb.log.info("Simultaneous BMC register writes: %s", tb.regs.collisions)


# ---------------------------------------------------------------------- FPGA ID

@cocotb.test()
@cocotb.parametrize(clocks=list(CLOCKS))
async def test_fpga_id(dut: Any, clocks: str) -> None:
    """The four DNA reads after reset, with slow and stalling PS responses."""
    tb = await get_testbench(dut, seed=scenario_seed(clocks, CLOCKS), clk_ps=CLOCKS[clocks][0],
                             axil_ps=CLOCKS[clocks][1], wait_id=False)
    tb.slave.set_ready_rates(0.3, 0.3, 0.3)
    tb.slave.set_latency(0, 30)
    fpga_id = await tb.wait_fpga_id()

    assert fpga_id == fpga_id_from_words(tb.dna), f"FPGA_ID 0x{fpga_id:032x}"
    assert [a.addr for a in tb.slave.log] == [DNA_BASE + 4 * i for i in range(4)], [str(a) for a in tb.slave.log]
    assert not await tb.status() & STATUS_BUSY
    await ClockCycles(dut.CLK, 200)
    assert len(tb.slave.log) == 4, "the FPGA ID must be read only once after reset"
    tb.check()


@cocotb.test()
async def test_fpga_id_error_response(dut: Any) -> None:
    """Error responses to the DNA reads do not block the FPGA ID (documented, RRESP is not checked)."""
    tb = await get_testbench(dut, seed=11, wait_id=False)
    tb.slave.set_response(SLVERR)
    fpga_id = await tb.wait_fpga_id()

    assert fpga_id == fpga_id_from_words(tb.dna)
    assert all(a.resp == SLVERR for a in tb.slave.log)
    tb.check()


@cocotb.test()
async def test_fpga_id_resets(dut: Any) -> None:
    """AXI_LITE_RESET reads the ID again, RESET alone only resynchronises the old one."""
    tb = await get_testbench(dut, seed=12)
    first = int(dut.FPGA_ID.value)

    new_dna = tb.load_dna()
    await tb.reset(host=False, axi_lite=True)
    assert not int(dut.FPGA_ID_VLD.value), "FPGA_ID_VLD must fall after AXI_LITE_RESET"
    second = await tb.wait_fpga_id()
    assert second == fpga_id_from_words(new_dna) != first
    assert len(tb.slave.log) == 8

    tb.load_dna()
    await tb.reset(host=True, axi_lite=False)
    assert await tb.wait_fpga_id() == second, "RESET of the CLK domain must not read the ID again"
    assert len(tb.slave.log) == 8
    tb.check()


@cocotb.test()
async def test_window_before_fpga_id(dut: Any) -> None:
    """Window accesses issued before the FPGA ID is read wait for it and are not mixed with the DNA reads."""
    tb = await get_testbench(dut, seed=13, wait_id=False)
    tb.slave.set_latency(60, 60)

    assert await tb.status() & STATUS_BUSY, "BUSY must be set until the FPGA ID is read"
    await tb.host_write(LOWER_ADDR, 0x1234_5000)
    tb.lower = 0x1234_5000
    await tb.window_write(0x10, 0xA5A5_0001)
    assert await tb.status() & STATUS_BUSY
    value = await tb.window_read(0x10)

    assert value == 0xA5A5_0001
    assert [a.addr for a in tb.slave.id_reads(tb.slave.epoch)] == [DNA_BASE + 4 * i for i in range(4)]
    await tb.wait_fpga_id()
    await tb.drain()
    tb.check()


# ---------------------------------------------------------------------- registers

@cocotb.test()
async def test_registers(dut: Any) -> None:
    """Register map: values, ignored MI_BE, reserved space, reset behaviour and the 12-bit address decoding."""
    tb = await get_testbench(dut, seed=21)
    rng = tb.rng

    await tb.status()
    assert await tb.host_read(UPPER_ADDR) == 0
    assert await tb.host_read(LOWER_ADDR) == 0

    for offset in [UPPER_ADDR, LOWER_ADDR] + [BMC_MI_OFFSET[name] for name in BMC_REGS]:
        for pattern in (0xFFFF_FFFF, 0x0000_0000, 0xA5A5_5A5A, rng.getrandbits(32)):
            be = rng.choice((0x0, 0x1, 0x6, 0x8, 0xF))
            await tb.host_write(offset, pattern, be)
            assert await tb.host_read(offset) == pattern, f"offset 0x{offset:03x}: MI_BE 0x{be:x} must be ignored"

    for offset in [0x01C, 0x020, 0x400, 0x7FC] + [rng.randrange(0x01C, WINDOW, 4) for _ in range(8)]:
        await tb.host_write(offset, rng.getrandbits(32))
        assert await tb.host_read(offset) == 0, f"reserved offset 0x{offset:03x}"
    await tb.host_write(STATUS, 0xFFFF_FFFF)
    await tb.status()

    bmc = {name: rng.getrandbits(32) for name in BMC_REGS}
    for name, value in bmc.items():
        await tb.host_write(BMC_MI_OFFSET[name], value)
    await tb.host_write(UPPER_ADDR, 0x1111_1111)
    await tb.host_write(LOWER_ADDR, 0x2222_2222)

    await tb.reset(host=True, axi_lite=False)
    assert await tb.host_read(UPPER_ADDR) == 0x1111_1111, "RESET must not clear the AXI_LITE_CLK registers"
    await tb.reset(host=False, axi_lite=True)
    await tb.wait_fpga_id()
    assert await tb.host_read(UPPER_ADDR) == 0
    assert await tb.host_read(LOWER_ADDR) == 0
    for name, value in bmc.items():
        assert await tb.host_read(BMC_MI_OFFSET[name]) == value, f"BMC_{name.upper()} must survive the resets"
    tb.check()


# ---------------------------------------------------------------------- address window

@cocotb.test()
async def test_window_addressing(dut: Any) -> None:
    """Window translation: UPPER_ADDR use, 2 KB alignment of LOWER_ADDR, truncation and partial reads."""
    tb = await get_testbench(dut, seed=31)
    rng = tb.rng
    windows = [(0, 0), (0xFFFF_FFFF, 0xFFFF_FFFF), (0x0000_0001, 0x8000_1234), (0x8000_0000, 0x0000_07FF),
               (rng.getrandbits(32), rng.getrandbits(32))]

    for upper, lower in windows:
        await tb.set_window(upper, lower)
        for offset in [0x000, 0x004, 0x400, 0x7FC] + [rng.randrange(0, WINDOW_SIZE, 4) for _ in range(4)]:
            await tb.window_write(offset, rng.getrandbits(32))
            await tb.window_read(offset)
        # MI_BE of a read is ignored, the whole word is read
        await tb.window_read(rng.randrange(0, WINDOW_SIZE, 4), rng.randint(1, 14))

    await tb.drain()
    tb.check()


@cocotb.test()
async def test_window_example(dut: Any) -> None:
    """The example of the documentation: LOWER_ADDR = 0x8000_1234, offsets 0x810 and 0xFFC."""
    tb = await get_testbench(dut, seed=32)
    await tb.set_window(0x0000_0001, 0x8000_1234)
    await tb.window_write(0x010, 0xCAFE_BABE)
    await tb.window_write(0x7FC, 0x1234_5678)
    await tb.drain()

    upper = 0x1_0000_0000 if tb.addr64 else 0
    assert [a.addr for a in tb.slave.window_accesses] == [upper | 0x8000_1010, upper | 0x8000_17FC]
    tb.check()


@cocotb.test()
async def test_window_strobes_and_errors(dut: Any) -> None:
    """Every MI_BE value reaches WSTRB, error responses complete the MI access normally."""
    tb = await get_testbench(dut, seed=33)
    await tb.set_window(0, 0x4000_0000)

    for be in range(16):
        await tb.window_write(4 * be, 0x0102_0304 * (be + 1) & 0xFFFF_FFFF, be)

    for resp in (SLVERR, DECERR):
        tb.slave.set_response(resp)
        await tb.window_write(0x100, 0xDEAD_BEEF)
        assert await tb.window_read(0x100) == tb.slave.read_word(tb.window_target(0x100))
    tb.slave.set_response(OKAY)

    await tb.drain()
    assert [a.resp for a in tb.slave.window_accesses[-4:]] == [SLVERR, SLVERR, DECERR, DECERR]
    tb.check()


@cocotb.test()
async def test_busy(dut: Any) -> None:
    """BUSY is set until a window write is issued on the AXI address channel."""
    tb = await get_testbench(dut, seed=41)
    await tb.set_window(0, 0x1000_0000)

    tb.slave.aw.hold = True
    await tb.window_write(0x20, 0x1)
    for _ in range(5):
        assert await tb.status() & STATUS_BUSY, "BUSY must be set while AW is stalled"
    tb.slave.aw.hold = False
    await tb.wait_not_busy()

    # The address handshake ends BUSY, the data phase does not matter.
    tb.slave.w.hold = True
    await tb.window_write(0x24, 0x2)
    for _ in range(100):
        if len(tb.slave.window_accesses) == 2:
            break
        await RisingEdge(dut.AXI_LITE_CLK)
    assert not await tb.status() & STATUS_BUSY, "BUSY must be cleared once AW is accepted"
    tb.slave.w.hold = False

    tb.slave.set_latency(50, 50)
    await tb.window_write(0x28, 0x3)
    await tb.drain()
    tb.check()


@cocotb.test()
async def test_busy_pending_writes(dut: Any) -> None:
    """BUSY with the largest number of window writes waiting for the AXI address channel.

    MI2AXI4 holds one write and the output pipe of MI_SPLITTER_PLUS_GEN three
    more, a fifth write would stay on the MI input and block the STATUS read.
    The AW channel is then released one write at a time. Regression test of
    the width of the BUSY counters: they must distinguish 4 pending writes
    from none.
    """
    tb = await get_testbench(dut, seed=43)
    await tb.set_window(0, 0x1000_0000)

    tb.slave.aw.hold = True
    for index in range(4):
        await tb.window_write(4 * index, tb.rng.getrandbits(32))
    await ClockCycles(dut.AXI_LITE_CLK, 50)

    for issued in range(4):
        assert await tb.status() & STATUS_BUSY, f"BUSY must be set with {4 - issued} writes pending"
        tb.slave.aw.hold = False
        while len(tb.slave.window_accesses) == issued:
            await RisingEdge(dut.AXI_LITE_CLK)
        tb.slave.aw.hold = True
        await ClockCycles(dut.AXI_LITE_CLK, 20)

    assert not await tb.status() & STATUS_BUSY
    tb.slave.aw.hold = False
    await tb.drain()
    tb.check()


@cocotb.test()
@cocotb.parametrize(clocks=list(CLOCKS))
async def test_window_access_after_move(dut: Any, clocks: str) -> None:
    """Window accesses right after UPPER_ADDR / LOWER_ADDR writes, with gaps of 0 to 7 CLK cycles.

    Regression test: the BUSY counters were cleared when the address register
    write reached the register, after the following window access had already
    been counted, and BUSY then stayed set forever.
    """
    tb = await get_testbench(dut, seed=42 + scenario_seed(clocks, CLOCKS), clk_ps=CLOCKS[clocks][0],
                             axil_ps=CLOCKS[clocks][1])
    for gap in range(8):
        for write in (True, False):
            await tb.set_window(tb.rng.getrandbits(32), tb.rng.getrandbits(32))
            await ClockCycles(dut.CLK, gap)
            if write:
                await tb.window_write(4 * gap, tb.rng.getrandbits(32))
            else:
                await tb.window_read(4 * gap)
            await tb.wait_not_busy()
    await tb.drain()
    tb.check()


# ---------------------------------------------------------------------- BMC mailbox

@cocotb.test()
async def test_bmc_mailbox(dut: Any) -> None:
    """Both directions for every register, 2 KB aliases, unmapped PS offsets and partial PS writes."""
    tb = await get_testbench(dut, seed=51)
    rng = tb.rng

    for name in BMC_REGS:
        value = rng.getrandbits(32)
        await tb.host_write(BMC_MI_OFFSET[name], value)
        # MI writes are posted by MI_ASYNC, the read back makes sure the write has reached the register.
        assert await tb.host_read(BMC_MI_OFFSET[name]) == value
        assert await tb.ps_read(BMC_PS_OFFSET[name]) == value, f"BMC_{name.upper()} host -> PS"
        alias = rng.getrandbits(21) << 11
        assert await tb.ps_read(alias | BMC_PS_OFFSET[name]) == value, f"BMC_{name.upper()} alias 0x{alias:x}"

        value = rng.getrandbits(32)
        await tb.ps_write(rng.getrandbits(21) << 11 | BMC_PS_OFFSET[name], value)
        assert await tb.host_read(BMC_MI_OFFSET[name]) == value, f"BMC_{name.upper()} PS -> host"

    before = {name: await tb.host_read(BMC_MI_OFFSET[name]) for name in BMC_REGS}
    for offset in [0x010, 0x014, 0x7FC] + [rng.randrange(0x010, 0x800, 4) for _ in range(8)]:
        await tb.ps_write(offset, rng.getrandbits(32))
        assert await tb.ps_read(offset) == 0, f"unmapped PS offset 0x{offset:03x}"
    assert {name: await tb.host_read(BMC_MI_OFFSET[name]) for name in BMC_REGS} == before

    # WSTRB is ignored, the whole WDATA word is stored (cocotbext-axi drives 0 on the unused lanes)
    await tb.ps_write(BMC_PS_OFFSET["control"], 0x1234_56AB, 1)
    value = await tb.host_read(BMC_MI_OFFSET["control"])
    assert value == 0x0000_00AB, f"BMC_CONTROL after a 1-byte PS write: 0x{value:08x}"
    tb.check()


@cocotb.test(timeout_time=2000, timeout_unit="us")
@cocotb.parametrize(clocks=list(CLOCKS))
async def test_bmc_simultaneous_writes(dut: Any, clocks: str) -> None:
    """Host and PS write the same register in the same cycle: the documented side wins.

    The relative start of the two writes is swept until the register block
    sees both in one cycle; the register model applies the priority and the
    following reads from both sides check it.
    """
    tb = await get_testbench(dut, seed=60 + scenario_seed(clocks, CLOCKS), clk_ps=CLOCKS[clocks][0],
                             axil_ps=CLOCKS[clocks][1])
    rng = tb.rng

    for name in BMC_REGS:
        for attempt in range(400):
            before = tb.regs.collisions[name]
            host_value, ps_value = rng.getrandbits(32), rng.getrandbits(32)
            host_delay, ps_delay = (attempt % 20), (attempt // 20)

            async def host_side() -> None:
                await ClockCycles(dut.CLK, host_delay)
                await tb.host_write(BMC_MI_OFFSET[name], host_value)

            async def ps_side() -> None:
                await ClockCycles(dut.AXI_LITE_CLK, ps_delay)
                await tb.ps_write(BMC_PS_OFFSET[name], ps_value)

            await Combine(cocotb.start_soon(host_side()), cocotb.start_soon(ps_side()))
            await ClockCycles(dut.AXI_LITE_CLK, 10)
            value = await tb.host_read(BMC_MI_OFFSET[name])
            await tb.ps_read(BMC_PS_OFFSET[name])

            if tb.regs.collisions[name] > before:
                winner = host_value if BMC_WRITE_PRIORITY[name] == "host" else ps_value
                assert value == winner, f"BMC_{name.upper()}: 0x{value:08x}, the {BMC_WRITE_PRIORITY[name]} write must win"
                break
        else:
            raise AssertionError(f"no simultaneous write to BMC_{name.upper()} was produced")
    tb.check()
    tb.log.info("Simultaneous writes: %s", tb.regs.collisions)


# ---------------------------------------------------------------------- resets

@cocotb.test()
@cocotb.parametrize(stalled=["read_address", "read_response", "write_address", "write_response"])
async def test_axi_lite_reset_recovery(dut: Any, stalled: str) -> None:
    """A PS that stops responding is recovered by AXI_LITE_RESET.

    A pending host read is answered by MI_ASYNC with its reset message. After
    the reset the FPGA ID is read again, BUSY clears and the window works.
    Regression test: the BUSY counters were not cleared by AXI_LITE_RESET.
    """
    tb = await get_testbench(dut, seed=71)
    await tb.set_window(0, 0x2000_0000)
    await tb.wait_not_busy()

    access, phase = stalled.split("_")
    if phase == "address":
        tb.slave.hold_address(True)
    else:
        tb.slave.hold_responses = True
    if access == "read":
        pending = cocotb.start_soon(tb.host_read(WINDOW + 0x40))
    else:
        await tb.host_write(WINDOW + 0x40, 0x1234_5678)
    await ClockCycles(dut.AXI_LITE_CLK, 50)
    if access == "read":
        assert not pending.done(), "the window read must wait for the PS"
    else:
        # BUSY covers the address phase of a write only
        busy = bool(await tb.host_read(STATUS) & STATUS_BUSY)
        assert busy == (phase == "address"), f"BUSY = {int(busy)} with the write stalled in the {phase} phase"

    tb.load_dna()
    await tb.reset(host=False, axi_lite=True)
    tb.slave.hold_address(False)
    tb.slave.hold_responses = False
    if access == "read":
        value = await pending
        assert value == 0xDEADFEED, f"pending read answered with 0x{value:08x}"

    await tb.wait_fpga_id()
    tb.restart_checks()
    await tb.wait_not_busy()
    await tb.set_window(0, 0x3000_0000)
    await tb.window_write(0x44, 0x5555_AAAA)
    assert await tb.window_read(0x44) == 0x5555_AAAA
    await tb.drain()
    tb.check()
