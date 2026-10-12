# cocotb_test.py:
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

from collections import deque
from dataclasses import dataclass
from random import randint
from typing import Any, Callable

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, RisingEdge
from cocotb.types import LogicArray
from cocotbext.ofm.base.protocol import optional_signal
from cocotbext.ofm.base.types import LogicArray2D
from cocotbext.ofm.mfb.drivers import MFBDriver
from cocotbext.ofm.mfb.monitors import MFBMonitor
from cocotbext.ofm.mfb.protocol import MfbProtocol
from cocotbext.ofm.mfb.transaction import MfbTransactionWithMeta
from cocotbext.ofm.ver.backpressure import BackpressureConfig, BackpressureGenerator
from cocotbext.ofm.ver.multibit_driver import MultiBitDriver, Patterns


class SwitchMfbProtocol(MfbProtocol):
    @optional_signal.read(put_with="SOF")
    def SEL(self, sigval: LogicArray) -> LogicArray:
        return sigval

    @SEL.write(put_with="SOF")
    def SEL(self, signal, value: LogicArray2D) -> None:
        signal.value = value.serialize()


# MFBDriver stores the value of each optional signal in its State. SEL is not
# a part of MFBDriver.State, so the State is extended here.
class SwitchMfbDriver(MFBDriver):
    @dataclass
    class State(MFBDriver.State):
        SEL : LogicArray2D = 0

    def _init_state(self) -> None:
        self.state = SwitchMfbDriver.State()


@dataclass(slots=True)
class SwitchTransaction(MfbTransactionWithMeta):
    sel: int = 0


class testbench():
    def __init__(self, dut: Any) -> None:
        self.dut = dut
        self.ports: int = int(dut.PORTS.value)
        self.meta_width: int = int(dut.META_WIDTH.value)
        mfb_params = {
            "regions"     : int(dut.REGIONS.value),
            "region_size" : int(dut.REGION_SIZE.value),
            "block_size"  : int(dut.BLOCK_SIZE.value),
            "item_width"  : int(dut.ITEM_WIDTH.value),
            "meta_width"  : self.meta_width,
        }

        self.stream_in: list[SwitchMfbDriver] = []
        self.stream_out: list[MFBMonitor] = []
        for p in range(self.ports):
            # Full input rate fills the FIFOs, which is the condition for a deadlock.
            self.stream_in.append(SwitchMfbDriver(dut, "RX_MFB", dut.CLK, array_idx=p, protocol=SwitchMfbProtocol, no_default_rate_limiter=True))
            monitor = MFBMonitor(dut, "TX_MFB", dut.CLK, array_idx=p, mfb_params=mfb_params, trans_type=MfbTransactionWithMeta)
            monitor.add_callback(self._check_callback(p))
            self.stream_out.append(monitor)

        # Packets from one RX input to one TX output keep their order. Packets
        # from different RX inputs can be mixed at the TX output.
        self.expected: dict[tuple[int, int], deque[MfbTransactionWithMeta]] = {
            (dst, src): deque() for dst in range(self.ports) for src in range(self.ports)
        }
        self.backpressure = MultiBitDriver(dut.TX_MFB_DST_RDY, dut.CLK, pattern=Patterns.random)

        self.pkts_sent = 0
        self.pkts_received = 0
        self.errors: list[str] = []

    def _check_callback(self, dst: int) -> Callable[[MfbTransactionWithMeta], None]:
        def check(tr: MfbTransactionWithMeta) -> None:
            self.pkts_received += 1
            src = tr.data[0]
            queue = self.expected.get((dst, src))
            if not queue:
                self.errors.append(f"TX{dst}: unexpected packet from RX{src}")
                return
            exp = queue.popleft()
            if tr.data != exp.data or tr.meta != exp.meta:
                self.errors.append(f"TX{dst}: packet from RX{src} differs\nexpected:\n{exp}\nreceived:\n{tr}")
        return check

    def send(self, src: int, dst: int, size: int, seq: int) -> None:
        data = bytes([src]) + seq.to_bytes(4, "little") + bytes(randint(0, 255) for _ in range(size - 5))
        meta = randint(0, 2**self.meta_width - 1)
        self.expected[(dst, src)].append(MfbTransactionWithMeta(data=data, meta=meta))
        self.stream_in[src].append(SwitchTransaction(data=data, meta=meta, sel=dst))
        self.pkts_sent += 1

    async def reset(self) -> None:
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 10)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)

    async def wait_for_all(self, stall_limit: int) -> None:
        """Wait until all packets are received. Fail when the TX outputs stop sending packets."""
        last_received = -1
        stall_cycles = 0
        while self.pkts_received < self.pkts_sent:
            await ClockCycles(self.dut.CLK, 100)
            if self.pkts_received == last_received:
                stall_cycles += 100
                assert stall_cycles < stall_limit, (
                    f"No packet came out for {stall_cycles} clock cycles, "
                    f"{self.pkts_received}/{self.pkts_sent} packets received (deadlock)."
                )
            else:
                stall_cycles = 0
            last_received = self.pkts_received


async def run_traffic(dut: Any, crossing: bool, pkt_count: int) -> testbench:
    cocotb.start_soon(Clock(dut.CLK, 5, unit="ns").start())
    tb = testbench(dut)
    await tb.reset()
    tb.backpressure.start(BackpressureGenerator(BackpressureConfig(1, 5, 0.5)))

    size_max = min(int(dut.PKT_SIZE_MAX.value), 512)
    for seq in range(pkt_count):
        for src in range(tb.ports):
            dst = randint(0, tb.ports - 1) if crossing else src
            tb.send(src, dst, randint(60, size_max), seq)

    await tb.wait_for_all(stall_limit=20_000)
    for queue in tb.expected.values():
        assert not queue, "Some expected packets were not received."
    assert not tb.errors, "\n".join(tb.errors[:10])
    return tb


@cocotb.test()
async def test_random_crossing(dut: Any, pkt_count: int = 3000) -> None:
    """Each packet goes to a random TX output while the TX outputs stop randomly."""
    await run_traffic(dut, crossing=True, pkt_count=pkt_count)


@cocotb.test()
async def test_no_crossing(dut: Any, pkt_count: int = 2000) -> None:
    """Each RX input sends only to its own TX output. No word is sent twice with a masked SOF."""
    masked_words = 0

    async def count_masked_words() -> None:
        nonlocal masked_words
        while True:
            await RisingEdge(dut.CLK)
            for p in range(int(dut.PORTS.value)):
                merger = dut.en_g.output_g[p].merge_i
                if merger.do_mask_leave.value == 1 and merger.dst_rdy_tx.value == 1:
                    masked_words += 1

    cocotb.start_soon(count_masked_words())
    await run_traffic(dut, crossing=False, pkt_count=pkt_count)
    assert masked_words == 0, f"{masked_words} words were sent with a masked SOF."
