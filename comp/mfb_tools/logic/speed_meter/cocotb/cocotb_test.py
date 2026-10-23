# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>

import random

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import Timer, RisingEdge, ClockCycles


async def read_mi(dut, addr):
    dut.MI_ADDR.value = addr
    dut.MI_RD.value = 1
    while dut.MI_ARDY.value == 0:
        await RisingEdge(dut.CLK)
    dut.MI_RD.value = 0

    while dut.MI_DRDY.value == 0:
        await RisingEdge(dut.CLK)

    data = int(dut.MI_DRD.value)
    await RisingEdge(dut.CLK)

    return data


async def send_mfb(dut, byte_cnt):
    bytes_in_word = 2**len(dut.RX_EOF_POS)

    dut.RX_SOF_POS.value = 0
    dut.RX_EOF_POS.value = (byte_cnt - 1) % (bytes_in_word)
    dut.RX_SOF.value = 1

    dut.RX_SRC_RDY.value = 1
    for i in range(byte_cnt):
        dut.RX_SOF.value = 1 if i < bytes_in_word else 0
        dut.RX_EOF.value = 1 if i == byte_cnt - 1 else 0

        if i % bytes_in_word == bytes_in_word - 1 or i == byte_cnt - 1:
            await RisingEdge(dut.CLK)

    dut.RX_SRC_RDY.value = 0


async def init(dut):
    # Start clock generator
    cocotb.start_soon(Clock(dut.CLK, 10, 'ns').start())

    # Do a reset
    dut.RST.value = 1
    await ClockCycles(dut.CLK, 2)
    dut.RST.value = 0
    await RisingEdge(dut.CLK)

    dut.RX_DST_RDY.value = 1


#@cocotb.test()
async def test_bytes_conut(dut):
    """Send transaction and check byte counter with MI READ"""
    await init(dut)

    for i in range(1650):
        await send_mfb(dut, i + 1)
    # MI latency of DUT is 3 CLK cycles
    await Timer(30, 'ns')

    # Check that transaction last 5 CLK cycles
    assert await read_mi(dut, 0) == 5
    # Check that transaction have 193 bytes
    assert await read_mi(dut, 8) == 16543


@cocotb.test()
async def test_reset(dut):
    """Check zero ticks after issuing reset"""
    await init(dut)

    await send_mfb(dut, 1987)

    dut.RST.value = 1
    await ClockCycles(dut.CLK, 1)
    dut.RST.value = 0
    # MI latency of DUT is 3 CLK cycles
    await ClockCycles(dut.CLK, 3)

    # Check that counter of ticks was zeroed
    assert await read_mi(dut, 0) == 0


BYTES_LOW = 0x08
BYTES_HIGH = 0x1C
TICKS = 0x00


async def mfb_backpressure(dut, rng):
    """Random RX_DST_RDY so that the meter has to count only the accepted words"""
    while True:
        dut.RX_DST_RDY.value = int(rng.random() < 0.7)
        await RisingEdge(dut.CLK)


async def mfb_send_packet(dut, rng, length):
    """Send one packet of the given size in bytes, word by word, holding each word until it is accepted"""
    regions = len(dut.RX_SOF)
    eof_width = len(dut.RX_EOF_POS) // regions
    region_bytes = 2 ** eof_width
    word_bytes = regions * region_bytes
    sent = 0
    while sent < length:
        remaining = length - sent
        sof = int(sent == 0)
        eof = 0
        eof_pos = 0
        if remaining <= word_bytes:
            eof_region = (remaining - 1) // region_bytes
            eof = 1 << eof_region
            eof_pos = ((remaining - 1) % region_bytes) << (eof_width * eof_region)
        while rng.random() < 0.2:
            dut.RX_SRC_RDY.value = 0
            await RisingEdge(dut.CLK)
        dut.RX_SOF.value = sof
        dut.RX_SOF_POS.value = 0
        dut.RX_EOF.value = eof
        dut.RX_EOF_POS.value = eof_pos
        dut.RX_SRC_RDY.value = 1
        while True:
            await RisingEdge(dut.CLK)
            if int(dut.RX_DST_RDY.value) == 1:
                break
        sent += min(remaining, word_bytes)
    dut.RX_SRC_RDY.value = 0
    dut.RX_SOF.value = 0
    dut.RX_EOF.value = 0


async def check_byte_counter(dut, preload=None):
    """Send random packets and check that the two MI words together give the total number of bytes"""
    rng = random.Random(random.getrandbits(64))
    await init(dut)
    cocotb.start_soon(mfb_backpressure(dut, rng))
    mi_width = len(dut.MI_DRD)
    counter = dut.mfb_speed_meter_i.bytes_cnt_reg
    width = len(counter)
    dut.RX_SRC_RDY.value = 0
    dut.MI_RD.value = 0
    dut.MI_WR.value = 0
    await ClockCycles(dut.CLK, 5)

    base = 0
    total = 0
    if preload is not None:
        # The counter is loaded close to a multiple of the MI word so that the packets cross it.
        base = preload(width, mi_width, rng)
        counter.value = base
        await RisingEdge(dut.CLK)
    for _ in range(40):
        length = rng.randint(1, 1500)
        await mfb_send_packet(dut, rng, length)
        total += length
    await ClockCycles(dut.CLK, 10)

    expected = (base + total) % 2 ** width
    low = await read_mi(dut, BYTES_LOW)
    high = await read_mi(dut, BYTES_HIGH)
    ticks = await read_mi(dut, TICKS)
    cocotb.log.info(f"CNT_BYTES_WIDTH={width} MI_DATA_WIDTH={mi_width} base={base} total={total} low={low} high={high} ticks={ticks}")
    assert low == expected % 2 ** mi_width
    assert high == expected >> mi_width
    if width <= mi_width:
        assert high == 0


@cocotb.test()
async def test_byte_counter_words(dut):
    """Bytes of random packets are read as a low word at 0x08 and a high word at 0x1C"""
    await check_byte_counter(dut)


@cocotb.test()
async def test_byte_counter_carry(dut):
    """The low word wraps and the high word counts the carry when the counter crosses the MI word boundary"""

    def preload(width, mi_width, rng):
        if width <= mi_width:
            return rng.randint(1, 2 ** width - 1)
        return (rng.randint(1, 2 ** (width - mi_width) - 1) << mi_width) - rng.randint(1, 1000)

    await check_byte_counter(dut, preload)
