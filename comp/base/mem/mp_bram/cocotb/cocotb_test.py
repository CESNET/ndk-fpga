"""
file: cocotb_test.py
author(s): Oliver Gurka <oliver.gurka@cesnet.cz>
description: Simple cocotb tests for multiport BRAM implemented using XOR

Copyright (C) 2024 CESNET z. s. p. o.
SPDX-License-Identifier: BSD-3-Clause
"""

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles


async def reset(dut):
    # Reset the design
    dut.RESET.value = 1
    await ClockCycles(dut.CLK, 5)
    dut.RESET.value = 0
    await RisingEdge(dut.CLK)


async def read(dut, port, addr):
    re = RisingEdge(dut.CLK)

    dut.RD_ADDR[port].value = addr
    dut.RD_EN[port].value = 1
    await re
    dut.RD_EN[port].value = 0

    while dut.RD_DATA_VLD[port].value != 1:
        await re

    return dut.RD_DATA[port].value


def start_clock(dut):
    # Set up the clock
    clock = Clock(dut.CLK, 10, units="ns")
    cocotb.start_soon(clock.start())


async def setup(dut):
    start_clock(dut)
    for i in range(dut.READ_PORTS.value):
        dut.RD_EN[i].value = 0
    for i in range(dut.WRITE_PORTS.value):
        dut.WR_EN[i].value = 0
    await reset(dut)


@cocotb.test()
async def test_simple(dut):
    await setup(dut)
    re = RisingEdge(dut.CLK)
    # Write some data
    dut.WR_EN[0].value = 1
    dut.WR_ADDR[0].value = 0
    dut.WR_DATA[0].value = 0xAA
    await re

    dut.WR_ADDR[0].value = 1
    dut.WR_DATA[0].value = 0xBB
    await RisingEdge(dut.CLK)

    dut.WR_EN.value = 0
    await RisingEdge(dut.CLK)

    assert (await read(dut, 0, 0)) == 0xAA
    assert (await read(dut, 1, 1)) == 0xBB


@cocotb.test()
async def test_parallel_write(dut):
    await setup(dut)
    re = RisingEdge(dut.CLK)

    # Write some data
    dut.WR_EN[0].value = 1
    dut.WR_ADDR[0].value = 42
    dut.WR_DATA[0].value = 0xAA

    dut.WR_EN[1].value = 1
    dut.WR_ADDR[1].value = 43
    dut.WR_DATA[1].value = 0xFF
    await re
    dut.WR_EN.value = 0

    if not dut.ONE_CLK_WRITE.value:
        await re

    assert (await read(dut, 0, 42)) == 0xAA
    assert (await read(dut, 1, 43)) == 0xFF


@cocotb.test()
async def test_parallel_write_read(dut):
    await setup(dut)
    re = RisingEdge(dut.CLK)

    # Write some data
    dut.WR_EN[0].value = 1
    dut.WR_ADDR[0].value = 52
    dut.WR_DATA[0].value = 0xAA

    dut.WR_EN[1].value = 1
    dut.WR_ADDR[1].value = 53
    dut.WR_DATA[1].value = 0xFF
    await re
    dut.WR_EN.value = 0

    if not dut.ONE_CLK_WRITE.value:
        await re

    dut.RD_ADDR[0] = 52
    dut.RD_ADDR[1] = 53
    dut.RD_EN = 3
    await re

    while dut.RD_DATA_VLD[0].value != 1:
        await re

    assert (dut.RD_DATA[0].value == 0xAA)
    assert (dut.RD_DATA[1].value == 0xFF)
