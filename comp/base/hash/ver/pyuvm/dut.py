# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025-2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from pyuvm import uvm_component
import cocotb
from cocotb.triggers import ClockCycles, RisingEdge
from cocotb.clock import Clock
from cocotb_bus.monitors import BusMonitor
from cocotbext.ofm.base.drivers import BusDriver
from tbench.sequences import HashSeqBaseItem, HashSeqEmptyItem

import spookyhash
from siphash import siphash_64, siphash_128, half_siphash_32, half_siphash_64
from ofm.comp.base.hash.chaskey.chaskey import Chaskey
from ofm.comp.base.hash.pcasd.pcasd import PCASD


class HashDUT(uvm_component):
    def build_phase(self):
        self.dut     = cocotb.top
        self.clock   = self.dut.CLK
        self.driver  = HashDriver(self.dut, "IN", self.clock)
        self.monitor = HashMonitor(self.dut, "OUT", self.clock)

        hash_func_name = self.dut.HASH_FUNCTION.value.decode("utf-8")

        if hash_func_name == "SPOOKYHASH":
            def hash_func(key: bytes, seed: bytes):
                return spookyhash.hash128(key, int.from_bytes(seed[0:8], "little"), int.from_bytes(seed[8:16], "little"))

        elif "SIPHASH" in hash_func_name:
            def hash_func(key: bytes, seed: bytes):
                compression_rounds  : int = self.dut.hash_function_g.siphash_i.COMPRESSION_ROUNDS.value
                finalization_rounds : int = self.dut.hash_function_g.siphash_i.FINALIZATION_ROUNDS.value
                word_width          : int = self.dut.hash_function_g.siphash_i.WORD_WIDTH.value

                match word_width:
                    case 32:
                        if self.dut.HASH_WIDTH.value > 32:
                            return int.from_bytes(half_siphash_64(seed[0:8], key, compression_rounds, finalization_rounds), "little")
                        else:
                            return int.from_bytes(half_siphash_32(seed[0:8], key, compression_rounds, finalization_rounds), "little")
                    case 64:
                        if self.dut.HASH_WIDTH.value > 64:
                            return int.from_bytes(siphash_128(seed, key, compression_rounds, finalization_rounds), "little")
                        else:
                            return int.from_bytes(siphash_64(seed, key, compression_rounds, finalization_rounds), "little")
                    case _:
                        raise ValueError(f"Unsupported word width {word_width}. Supported word widths are 32 and 64.")

        elif "CHASKEY" in hash_func_name:
            def hash_func(key: bytes, seed: bytes):
                rounds: int = self.dut.hash_function_g.chaskey_i.ROUNDS.value
                return int.from_bytes(Chaskey.Hash128(key, seed, rounds), "little")

        elif "PCASD" in hash_func_name or "PCARX" in hash_func_name:
            def hash_func(key: bytes, seed: bytes):
                ca_rounds   : int = self.dut.hash_function_g.pcasd_i.CA_ROUNDS.value
                rd_rounds   : int = self.dut.hash_function_g.pcasd_i.MIX_ROUNDS.value
                block_width : int = self.dut.hash_function_g.pcasd_i.BLOCK_WIDTH.value // 8
                mix_func    : str = self.dut.hash_function_g.pcasd_i.MIX_FUNCTION.value.decode()

                pcasd: PCASD = PCASD(seed, ca_rounds, rd_rounds, block_width, mix_function=mix_func, multithreaded=False)

                return int.from_bytes(pcasd.hash(key), "little")

        else:
            raise NotImplementedError(f"Unsupported hash function '{hash_func_name}'.")

        self.hash = hash_func

    def start_of_simulation_phase(self):
        cocotb.start_soon(Clock(self.clock, 5, unit="ns").start())

    @property
    def key_width(self):
        return len(self.driver.bus.key)

    @property
    def seed_width(self):
        return len(self.driver.bus.seed)

    @property
    def hash_width(self):
        return len(self.monitor.bus.hash)

    @property
    def meta_width(self):
        if hasattr(self.driver.bus, "meta"):
            return len(self.driver.bus.meta)
        else:
            return 0

    async def reset(self):
        self.dut.RESET.value = 1
        await ClockCycles(self.clock, 10)
        self.dut.RESET.value = 0
        await RisingEdge(self.clock)


class HashDriver(BusDriver):
    _signals = ["key", "seed", "meta", "valid"]

    def __init__(self, entity, name, clock, array_idx=None, **kwargs):
        super().__init__(entity, name, clock, array_idx, **kwargs)
        self._clear_control_signals()

    def _clear_control_signals(self):
        for name in self._signals:
            if hasattr(self.bus, name):
                sig = getattr(self.bus, name)
                sig.value = 0

    async def _driver_send(self, transaction: HashSeqBaseItem, sync: bool = True):
        for name, value in transaction.to_dict().items():
            if hasattr(self.bus, name):
                sig = getattr(self.bus, name)
                sig.value = value

        self.bus.valid.value = 1 if not isinstance(transaction, HashSeqEmptyItem) else 0

        await self._clk_re

        self._clear_control_signals()


class HashMonitor(BusMonitor):
    _signals = ["hash", "meta", "valid"]

    def __init__(self, entity, name, clock, reset=None, reset_n=None, callback=None, event=None, **kwargs):
        super().__init__(entity, name, clock, reset, reset_n, callback, event, **kwargs)
        self.trans_cnt = 0

    async def _monitor_recv(self):
        clk_re = RisingEdge(self.clock)

        while True:
            await clk_re

            transaction = dict()

            if self.bus.valid.value == 1:
                for name in self._signals:
                    if hasattr(self.bus, name) and name != "valid":
                        sig = getattr(self.bus, name)
                        transaction[name] = sig.value.to_unsigned()

                self.log.debug(f"received {transaction=}")

                self._recv(transaction)
                self.trans_cnt += 1
