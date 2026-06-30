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
from siphash import siphash_64, siphash_128, half_siphash_32, half_siphash_64
from ofm.comp.base.hash.chaskey.chaskey import Chaskey


class HashDriver(BusDriver):
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


class HashMonitor(BusMonitor):
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
        self.stream_in  : HashDriver  = HashDriver(dut, "IN", dut.CLK)
        self.stream_out : HashMonitor = HashMonitor(dut, "OUT", dut.CLK)

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
    seed_width = len(tb.stream_in.bus.SEED)
    meta_width = len(tb.stream_in.bus.META)
    hash_width = len(tb.stream_out.bus.HASH)

    key_width_bytes  = ceildiv(8, key_width)
    seed_width_bytes = ceildiv(8, seed_width)

    match (hash_func_name := dut.HASH_FUNCTION.value.decode("utf-8")):
        case "SPOOKYHASH":
            def hash_func(key: bytes, seed: bytes):
                return spookyhash.hash128(key, int.from_bytes(seed[0:8], "little"), int.from_bytes(seed[8:16], "little"))

        case "SIPHASH_2_4" | "SIPHASH_4_8" | "HALFSIPHASH_2_4" | "HALFSIPHASH_4_8":
            def hash_func(key: bytes, seed: bytes):
                compression_rounds  : int = dut.hash_function_g.siphash_i.COMPRESSION_ROUDS.value
                finalization_rounds : int = dut.hash_function_g.siphash_i.FINALIZATION_ROUNDS.value
                word_width          : int = dut.hash_function_g.siphash_i.WORD_WIDTH.value

                match word_width:
                    case 32:
                        if dut.HASH_WIDTH.value > 32:
                            return int.from_bytes(half_siphash_64(seed[0:8], key, compression_rounds, finalization_rounds), "little")
                        else:
                            return int.from_bytes(half_siphash_32(seed[0:8], key, compression_rounds, finalization_rounds), "little")
                    case 64:
                        if dut.HASH_WIDTH.value > 64:
                            return int.from_bytes(siphash_128(seed, key, compression_rounds, finalization_rounds), "little")
                        else:
                            return int.from_bytes(siphash_64(seed, key, compression_rounds, finalization_rounds), "little")
                    case _:
                        raise ValueError(f"Unsupported word width {word_width}. Supported word widths are 32 and 64.")
        case "CHASKEY" | "CHASKEY_LTS":
            def hash_func(key: bytes, seed: bytes):
                rounds: int = dut.hash_function_g.chaskey_i.ROUNDS.value
                return int.from_bytes(Chaskey.Hash128(key, seed, rounds), "little")

        case _:
            raise NotImplementedError(f"Unsupported hash function '{hash_func_name}'.")

    for i in range(trans_cnt):
        transaction = dict()
        transaction["KEY"]  = randint(0, 2**key_width-1)
        transaction["SEED"] = randint(0, 2**seed_width-1)
        transaction["META"] = randint(0, 2**meta_width-1)

        #cocotb.log.info(f"{i=}, {transaction=}")

        hash = hash_func(transaction["KEY"].to_bytes(key_width_bytes, "little"), transaction["SEED"].to_bytes(seed_width_bytes, "little"))

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
