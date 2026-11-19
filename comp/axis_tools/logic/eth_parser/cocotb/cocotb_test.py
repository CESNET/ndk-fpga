# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Cocotb tests for AXIS_ETH_PARSER_GEN and AXIS_ETH_PARSER (through AXIS_ETH_PARSER_TB).

Tests:
- run_test_all_stacks: Every combination of header protocols
- run_test_all_stacks_cut: Every combination, cut inside and at the end of each header
- run_test_base: Random header stacks with moderate backpressure
- run_test_headers_backpressure: Strong backpressure on HDR_READY
- run_test_malformed: Random header bytes and packets cut short
"""

import os
import random
from collections import deque
from typing import Iterable, Optional

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, RisingEdge
from cocotbext.ofm.axi4stream.drivers import Axi4StreamMaster, Axi4StreamSlave
from cocotbext.ofm.axi4stream.transaction import Axi4StreamTransaction
from cocotbext.ofm.utils.hex_formatter import format_bytes
from cocotbext.ofm.ver.backpressure import BackpressureConfig, apply_backpressure

from model import EXTRACT_BYTES, PROTO_NAMES, ParserModel, ParserResult
from pkt_gen import all_stacks, build_packet, build_stack, cut_lengths, malform_packet


class Testbench:
    """Drivers, header monitor and comparison with the model."""

    def __init__(self, dut):
        self.dut = dut
        self.rx_driver = Axi4StreamMaster(dut, "RX_AXI", dut.CLK, rate_limiter_config=dict(max_idles=5, zero_idles_chance=50))
        self.tx_driver = Axi4StreamSlave(dut, "TX_AXI", dut.CLK)
        self.expected: deque = deque()
        self.checked = 0
        self.errors = 0

    async def reset(self):
        self.dut.HDR_READY.value = 1
        self.dut.TX_AXI_TREADY.value = 1
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 8)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)

        # The configuration outputs have their values only after the simulation starts
        cfg = int(self.dut.CFG_PROTOCOLS.value)
        stages = len(self.dut.HDR_FOUND)
        self.protocols = [(cfg >> (8 * i)) & 0xFF for i in range(stages)]
        self.pkt_mtu = int(self.dut.CFG_PKT_MTU.value)
        self.data_width = len(self.dut.HDR_DATA) // stages
        self.offset_width = len(self.dut.HDR_OFFSET) // stages
        self.model = ParserModel(self.protocols, self.pkt_mtu)
        cocotb.log.info("Protocols: " + "-".join(PROTO_NAMES[p] for p in self.protocols))

    def send(self, pkt: bytes):
        self.expected.append(self.model.parse(pkt))
        self.rx_driver.append(Axi4StreamTransaction(TDATA=pkt))

    async def monitor(self):
        while True:
            await RisingEdge(self.dut.CLK)
            if self.dut.HDR_VLD.value == 1 and self.dut.HDR_READY.value == 1:
                self.compare(int(self.dut.HDR_FOUND.value), int(self.dut.HDR_DATA.value), int(self.dut.HDR_OFFSET.value))

    def compare(self, found: int, data: int, offset: int):
        if not self.expected:
            self.errors += 1
            raise AssertionError("HDR_VLD is set, but no packet is expected")

        exp: ParserResult = self.expected.popleft()
        errors = []
        for i, (proto, stage) in enumerate(zip(self.protocols, exp.stages)):
            dut_found = (found >> i) & 1
            if dut_found != int(stage.found):
                errors.append(f"stage {i} ({PROTO_NAMES[proto]}): found {dut_found}, expected {int(stage.found)}")
                continue
            if not stage.found:
                continue
            nbytes = EXTRACT_BYTES[proto]
            dut_data = ((data >> (i * self.data_width)) & ((1 << (nbytes * 8)) - 1)).to_bytes(nbytes, "little")
            dut_offset = (offset >> (i * self.offset_width)) & ((1 << self.offset_width) - 1)
            if dut_data != stage.data:
                errors.append(f"stage {i} ({PROTO_NAMES[proto]}): data {dut_data.hex()}, expected {stage.data.hex()}")
            if dut_offset != stage.offset:
                errors.append(f"stage {i} ({PROTO_NAMES[proto]}): offset {dut_offset}, expected {stage.offset}")

        if errors:
            self.errors += 1
            msg = f"Packet {self.checked}:\n" + "\n".join(errors) + "\n" + format_bytes(exp.packet, label="Packet")
            raise AssertionError(msg)
        self.checked += 1


def random_packets(pkt_count: int, malform_prob: float = 0.0) -> Iterable[bytes]:
    pkt_count = int(os.environ.get("COCOTB_PKT_COUNT", pkt_count))
    for _ in range(pkt_count):
        if random.random() < malform_prob:
            yield malform_packet(build_packet(malformed=True))
        else:
            yield build_packet()


def stack_packets(cut: bool) -> Iterable[bytes]:
    for st in all_stacks():
        pkt, ends = build_stack(st)
        if not cut:
            yield pkt
            continue
        for length in cut_lengths(len(pkt), ends):
            yield pkt[:length]


async def _run_test(
    dut,
    packets: Iterable[bytes],
    tx_cfg: Optional[BackpressureConfig],
    hdr_cfg: Optional[BackpressureConfig]
):
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())

    tb = Testbench(dut)
    await tb.reset()
    cocotb.start_soon(tb.monitor())
    tx_task = cocotb.start_soon(apply_backpressure(dut.TX_AXI_TREADY, dut.CLK, tx_cfg))
    hdr_task = cocotb.start_soon(apply_backpressure(dut.HDR_READY, dut.CLK, hdr_cfg))

    pkt_count = 0
    found_patterns = set()
    for pkt in packets:
        tb.send(pkt)
        found_patterns.add(tuple(st.found for st in tb.expected[-1].stages))
        pkt_count += 1
    cocotb.log.info(f"Sent {pkt_count} packets, {len(found_patterns)} different sets of found headers")

    timeout = 0
    while tb.checked < pkt_count and tb.errors == 0 and timeout < 100000:
        await ClockCycles(dut.CLK, 10)
        timeout += 1

    tx_task.cancel()
    hdr_task.cancel()

    cocotb.log.info(f"Checked {tb.checked}/{pkt_count} packets")
    if tb.errors > 0:
        raise AssertionError(f"Test failed with {tb.errors} errors")
    if tb.checked < pkt_count:
        raise AssertionError(f"Only {tb.checked}/{pkt_count} packets checked")


@cocotb.test()
async def run_test_all_stacks(dut):
    """Every combination of header protocols. all_stacks lists them."""
    await _run_test(dut, stack_packets(cut=False), BackpressureConfig(1, 5, 0.5), BackpressureConfig(1, 5, 0.5))


@cocotb.test()
async def run_test_all_stacks_cut(dut):
    """Every combination of header protocols, cut inside and at the end of each header."""
    await _run_test(dut, stack_packets(cut=True), BackpressureConfig(1, 5, 0.5), BackpressureConfig(1, 5, 0.5))


@cocotb.test()
async def run_test_base(dut, pkt_count=3000):
    """Random header stacks with moderate backpressure on TX and HDR_READY."""
    await _run_test(dut, random_packets(pkt_count), BackpressureConfig(1, 5, 0.5), BackpressureConfig(1, 5, 0.5))


@cocotb.test()
async def run_test_headers_backpressure(dut, pkt_count=2000):
    """Strong backpressure on HDR_READY, light backpressure on TX."""
    await _run_test(dut, random_packets(pkt_count), BackpressureConfig(1, 5, 0.1), BackpressureConfig(20, 200, 0.9))


@cocotb.test()
async def run_test_malformed(dut, pkt_count=3000):
    """Random header bytes and packets cut short."""
    await _run_test(dut, random_packets(pkt_count, 0.5), BackpressureConfig(1, 5, 0.5), BackpressureConfig(1, 5, 0.5))
