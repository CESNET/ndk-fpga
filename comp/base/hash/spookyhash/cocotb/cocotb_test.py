# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotbext.ofm.base.drivers import BusDriver
from cocotbext.ofm.utils.math import ceildiv, bitmask
from cocotb_bus.monitors import BusMonitor
from cocotb_bus.scoreboard import Scoreboard
from random import randint
import spookyhash


class SpookyDriver(BusDriver):
    _signals = ["KEY", "SEED", "META", "VALID"]

    def __init__(self, entity, name, clock, array_idx=None, **kwargs):
        super().__init__(entity, name, clock, array_idx, **kwargs)
        self._clear_control_signals()

    def _clear_control_signals(self):
        for name in self._signals:
            if hasattr(self.bus, name):
                sig = getattr(self.bus, name)
                sig.value = 0

    async def _driver_send(self, transaction: dict, sync: bool = True):
        for name, value in transaction.items():
            if hasattr(self.bus, name):
                sig = getattr(self.bus, name)
                sig.value = value

        self.bus.VALID.value = 1

        await self._clk_re

        self._clear_control_signals()


class SpookyMonitor(BusMonitor):
    _signals = ["HASH", "META", "VALID"]

    def __init__(self, entity, name, clock, reset=None, reset_n=None, callback=None, event=None, **kwargs):
        super().__init__(entity, name, clock, reset, reset_n, callback, event, **kwargs)
        self.trans_cnt = 0

    async def _monitor_recv(self):
        clk_re = RisingEdge(self.clock)

        while True:
            await clk_re

            transaction = dict()

            if self.bus.VALID.value.integer == 1:
                for name in self._signals:
                    if hasattr(self.bus, name) and name != "VALID":
                        sig = getattr(self.bus, name)
                        transaction[name] = sig.value.integer

                self.log.debug(f"received {transaction=}")

                self._recv(transaction)
                self.trans_cnt += 1
                transaction = dict()


class testbench():
    def __init__(self, dut, debug=False):
        self.dut = dut
        self.stream_in  : SpookyDriver  = SpookyDriver(dut, "IN", dut.CLK)
        self.stream_out : SpookyMonitor = SpookyMonitor(dut, "OUT", dut.CLK)

        if debug:
            self.stream_in.log.setLevel(cocotb.logging.DEBUG)
            self.stream_out.log.setLevel(cocotb.logging.DEBUG)

        # Create a scoreboard on the stream_out bus
        self.pkts_sent = 0
        self.expected_output = list()
        self.scoreboard = Scoreboard(dut)
        self.scoreboard.add_interface(self.stream_out, self.expected_output)

    def model(self, transaction: dict):
        """Model the DUT based on the input transaction"""
        self.expected_output.append(transaction)

    async def reset(self):
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 10)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)


@cocotb.test()
async def run_test(dut, trans_cnt=10000):
    # Start clock generator
    cocotb.start_soon(Clock(dut.CLK, 5, units="ns").start())

    tb = testbench(dut, debug=False)

    await tb.reset()

    key_width  = len(tb.stream_in.bus.KEY)
    hash_width = len(tb.stream_in.bus.SEED)
    meta_width = len(tb.stream_in.bus.META)
    hash_width = len(tb.stream_out.bus.HASH)

    key_width_bytes = ceildiv(8, key_width)

    for i in range(trans_cnt):
        transaction = dict()
        transaction["KEY"]   = randint(0, 2**key_width-1)
        transaction["SEED"]  = randint(0, 2**hash_width-1)
        transaction["META"]  = randint(0, 2**meta_width-1)

        cocotb.log.info(f"{i=}, {transaction=}")

        if hash_width > 64:
            seed1 = transaction["SEED"] & 0xFFFFFFFFFFFFFFFF
            seed2 = (transaction["SEED"] >> 64) & 0xFFFFFFFFFFFFFFFF
        else:
            seed1 = transaction["SEED"]
            seed2 = seed1

        hash = spookyhash.hash128(transaction["KEY"].to_bytes(key_width_bytes, "little"), seed1, seed2)

        reference = dict()
        reference["HASH"] = hash & bitmask(hash_width)
        reference["META"] = transaction["META"]

        tb.model(reference)
        tb.stream_in.append(transaction)

    # waiting for all transactions to be received
    last_num = 0

    while tb.stream_out.trans_cnt < trans_cnt:
        if (tb.stream_out.trans_cnt // 1000) > last_num:
            last_num = tb.stream_out.trans_cnt // 1000
            cocotb.log.info("Number of transactions tb.stream_out.trans_cnt: %d/%d" % (tb.stream_out.trans_cnt, trans_cnt))
        await ClockCycles(dut.CLK, 100)

    raise tb.scoreboard.result
