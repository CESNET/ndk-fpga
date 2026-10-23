# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025-2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

import cocotb
import logging
from cocotb.types import LogicArray
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotbext.ofm.mi.drivers import MIRequestDriverAgent, MIResponseDriverAgent
from cocotbext.ofm.mi.proxymonitor import MIProxyMonitor
from cocotbext.ofm.mi.monitors import MIMonitor
from cocotbext.ofm.ver.backpressure import BackpressureGenerator, BackpressureConfig
from cocotbext.ofm.ver.generators import random_packets
from cocotbext.ofm.utils.math import ceildiv
from cocotb_bus.drivers import BitDriver
from cocotb_bus.scoreboard import Scoreboard
from cocotbext.ofm.mi.transaction import MiRequestTransaction, MiResponseTransaction, MiTransaction, MiTransactionType
from cocotbext.ofm.utils.signals import filter_bytes_by_bitmask

from random import choice, randint, randbytes


class testbench():
    def __init__(self, dut, debug=False, use_scoreboard=True):
        self.dut = dut
        self.request_stream_in = MIRequestDriverAgent(dut, "IN", dut.CLK)
        self.response_stream_out = MIMonitor(dut, "OUT", dut.CLK)
        self.response_proxy = MIProxyMonitor(self.response_stream_out, MiTransactionType.Request)
        self.response_stream_in = MIResponseDriverAgent(dut, "OUT", dut.CLK)
        self.request_stream_out = MIMonitor(dut, "IN", dut.CLK)
        self.request_proxy = MIProxyMonitor(self.request_stream_out, MiTransactionType.Response)

        self.backpressure = BitDriver(dut.OUT_ARDY, dut.CLK)

        # Create a scoreboard on the response_stream_out bus
        self.pkts_sent = 0
        self.expected_output = []
        if use_scoreboard:
            self.scoreboard = Scoreboard(dut)
            self.scoreboard.add_interface(self.response_proxy, self.expected_output)
            self.scoreboard.add_interface(self.request_proxy, self.expected_output)

        if debug:
            self.request_stream_in.log.setLevel(logging.DEBUG)
            self.response_stream_out.log.setLevel(logging.DEBUG)

    def model(self, test_trans: MiTransaction):
        """Model the DUT based on the input transaction"""

        self.expected_output.append(test_trans)
        self.pkts_sent += 1

    async def reset(self):
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 2)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)


@cocotb.test()
async def run_test(dut, pkt_count: int = 1000, item_width_min: int = 1, item_width_max: int = 32):
    # Start clock generator
    cocotb.start_soon(Clock(dut.CLK, 5, unit='ns').start())
    tb = testbench(dut, debug=False)
    await tb.reset()

    tb.backpressure.start(BackpressureGenerator(BackpressureConfig(1, 5, 0.5)))

    item_count = 0
    trans_cntr = 0

    for transaction in random_packets(item_width_min, item_width_max, pkt_count):
        trans_cntr += 1
        request_type = choice([MiTransactionType.Request, MiTransactionType.Response])
        start_addr = randint(0, 2**(tb.request_stream_in.addr_width*8)-1)

        addr = start_addr
        offset_transaction = transaction
        byte_enable = LogicArray("1" * len(transaction))

        start_offset = addr % tb.request_stream_in.data_width
        end_offset = -(addr + len(offset_transaction)) % tb.request_stream_in.data_width

        offset_transaction = bytes(start_offset) + offset_transaction + bytes(end_offset)
        byte_enable = LogicArray(("0" * start_offset) + str(byte_enable) + ("0" * end_offset))
        addr = addr - start_offset

        cycles = ceildiv(bus_width=tb.request_stream_in.data_width, transaction_len=len(offset_transaction))

        for i in range(cycles):
            data = offset_transaction[i*tb.request_stream_in.data_width:(i+1)*tb.request_stream_in.data_width]

            be_slice = LogicArray(str(byte_enable)[i*tb.request_stream_in.data_width:(i+1)*tb.request_stream_in.data_width][::-1]).to_unsigned()
            enabled_data = filter_bytes_by_bitmask(data, be_slice)

            if len(enabled_data) == 0:
                continue

            test_trans = MiTransaction()
            test_trans.trans_type = request_type
            test_trans.addr = addr + i*tb.request_stream_in.addr_width
            test_trans.data = enabled_data
            test_trans.be = be_slice
            tb.model(test_trans)
            item_count += 1

        request_trans = MiRequestTransaction()
        request_trans.trans_type = request_type
        request_trans.addr = start_addr
        request_trans.data = transaction
        request_trans.data_len = len(transaction)

        response_trans = MiResponseTransaction()
        response_trans.trans_type = request_type
        response_trans.data = offset_transaction
        response_trans.be = byte_enable.to_unsigned()

        cocotb.log.debug(f"generated transaction: {transaction.hex()}")
        tb.request_stream_in.append(request_trans)
        tb.response_stream_in.append(response_trans)

    last_num = 0
    stream_out_item_cnt = tb.response_proxy.item_cnt + tb.request_proxy.item_cnt

    while stream_out_item_cnt < item_count:
        if stream_out_item_cnt // 1000 > last_num:
            last_num = stream_out_item_cnt // 1000
            cocotb.log.info(f"Number of transactions processed: {stream_out_item_cnt}/{item_count}")
        await ClockCycles(dut.CLK, 100)
        stream_out_item_cnt = tb.response_proxy.item_cnt + tb.request_proxy.item_cnt

    raise tb.scoreboard.result


def expected_words(width, addr, byte_count, byte_enable):
    """(word address, byte enable of the bus word) for every bus word of an unaligned request."""
    start = addr % width
    words = []
    for w in range(ceildiv(width, start + byte_count)):
        mask = 0
        for j in range(width):
            k = w * width + j - start
            if 0 <= k < byte_count and (byte_enable >> k) & 1:
                mask |= 1 << j
        words.append((addr - start + w * width, mask))
    return words


@cocotb.test()
async def run_partial_byte_enable_test(dut, request_count: int = 200):
    """Requests with partial byte enables reach the bus word by word with the enabled bytes at the right lanes."""
    cocotb.start_soon(Clock(dut.CLK, 5, unit='ns').start())
    tb = testbench(dut, debug=False, use_scoreboard=False)
    await tb.reset()
    tb.backpressure.start(BackpressureGenerator(BackpressureConfig(1, 5, 0.5)))

    observed = []
    tb.response_stream_out.add_callback(observed.append)
    width = tb.request_stream_in.data_width

    for n in range(request_count):
        byte_count = randint(1, 3 * width)
        addr = randint(0, 2**(tb.request_stream_in.addr_width * 8) - 1 - 3 * width)
        byte_enable = randint(0, 2**byte_count - 1)
        words = expected_words(width, addr, byte_count, byte_enable)
        start = addr % width
        padded = randbytes(len(words) * width)
        observed.clear()

        if choice([True, False]):
            data = padded[start:start + byte_count]
            await tb.request_stream_in.write(addr, data, byte_enable=byte_enable)
            aligned = bytes(start) + data + bytes(len(words) * width - start - byte_count)
            expected = [(a, m, filter_bytes_by_bitmask(aligned[i * width:(i + 1) * width], m)) for i, (a, m) in enumerate(words)]
            while len(observed) < len(words):
                await ClockCycles(dut.CLK, 1)
        else:
            cocotb.start_soon(tb.response_stream_in.write(padded))
            read_data = await tb.request_stream_in.read(addr, byte_count, byte_enable=byte_enable)
            assert read_data == padded[start:start + byte_count], f"request {n}: read data differ"
            expected = [(a, m, filter_bytes_by_bitmask(padded[i * width:(i + 1) * width], m)) for i, (a, m) in enumerate(words)]

        got = [(t.addr, t.be, t.data) for t in observed]
        assert got == expected, f"request {n} ({addr=:#x}, {byte_count=}, {byte_enable=:#x}): bus words {got}, expected {expected}"
