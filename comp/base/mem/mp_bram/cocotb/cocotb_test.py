# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025-2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>


import cocotb
import logging
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotbext.ofm.mp_bram.controller import MP_BRAM_Controller
from cocotbext.ofm.utils.ram import VWWRAM
from cocotbext.ofm.ver.generators import random_packets
from random import randint


class testbench():
    def __init__(self, dut, debug=False):
        self.dut = dut
        self.stream_in = MP_BRAM_Controller(dut, "", dut.CLK)

        self.ref_ram = VWWRAM(capacity=2**len(self.stream_in.bus.WR_ADDR[0]),
                              word_width=len(self.stream_in.bus.WR_DATA[0]),
                              block_width=dut.BLOCK_WIDTH.value if dut.BLOCK_ENABLE.value else None)

        if debug:
            self.stream_in.log.setLevel(logging.DEBUG)

    async def reset(self):
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 2)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)


async def write_read_test(dut, pkt_count=1000, item_width_min=1, item_width_max=16, parallel_write=False, parallel_read=False):
    # Start clock generator
    cocotb.start_soon(Clock(dut.CLK, 5, unit='ns').start())
    tb = testbench(dut)
    await tb.reset()
    await tb.stream_in.clear_memory()

    addr_width = len(tb.stream_in.bus.WR_ADDR[0])

    for i, transaction in enumerate(random_packets(item_width_min, item_width_max, pkt_count)):
        cocotb.log.debug(f"generated transaction: {transaction.hex()}")

        address = randint(0, (2**addr_width-1)-(len(transaction)*8))

        await tb.stream_in.write(address, transaction, parallel=parallel_write)

        tb.ref_ram.write(address, transaction) # writting transaction to reference RAM

        output = await tb.stream_in.read(address, len(transaction), parallel=parallel_read)
        cocotb.log.debug(f"received transaction:  {output.hex()}")

        assert output == transaction, f"Expected {transaction.hex()}, got {output.hex()}"

        if i % 100 == 0:
            cocotb.log.info(f"Processed requests {i}/{pkt_count}.")

    cocotb.log.info("--------------------Comparing end state of reference RAM and simulated RAM--------------------")

    for i in range(2**addr_width):
        ref_word = tb.ref_ram.read_word(i)
        sim_word = await tb.stream_in.read_word(i, 0)

        assert ref_word == sim_word, f"On address {i} reference RAM has {ref_word}, but simulated RAM has {sim_word}."


@cocotb.test()
async def test_simple(dut):
    "Serial write and read"
    await write_read_test(dut)


@cocotb.test()
async def test_parallel_write(dut):
    "Parallel write, serial read"
    await write_read_test(dut, parallel_write=True)


@cocotb.test()
async def test_parallel_read(dut):
    "Serial write, parallel read"
    await write_read_test(dut, parallel_read=True)


@cocotb.test()
async def test_parallel_write_read(dut):
    "Parallel write and read"
    await write_read_test(dut, parallel_write=True, parallel_read=True)
