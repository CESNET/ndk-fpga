# testbench.py: Testbench of the TX_MAC_LITE_ADAPTER_SAXIS verification
# Copyright (C) 2026 DynaNIC Semiconductors, Ltd.
# Author(s): Vlastimil Kosar <kosar@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

"""MFBDriver -> TX_MAC_LITE_ADAPTER_SAXIS -> Segmented AXI-Stream monitor and protocol checker.

The adapter only reformats the frames, so the reference model is the
identity: every frame leaves in order, unchanged and without ERR.
"""

from collections import Counter, deque
from dataclasses import dataclass
from typing import Any, Optional

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge
from cocotbext.ofm.base.transaction import IdleTransactionFactory
from cocotbext.ofm.mfb.drivers import MFBDriver
from cocotbext.ofm.mfb.protocol import MfbProtocol
from cocotbext.ofm.mfb.transaction import MfbTransaction
from cocotbext.ofm.saxis.checker import SAXISProtocolChecker
from cocotbext.ofm.saxis.monitors import SAXISMonitor
from cocotbext.ofm.utils.hex_formatter import format_bytes


class TxMfbProtocol(MfbProtocol):
    BLOCK_SIZE: int = 8
    ITEM_WIDTH: int = 8


@dataclass
class MfbIdles:
    """Idles inserted by MFBDriver before a frame.

    The idle length is in bytes and rounded up to whole 8 B blocks; up to 63 B
    moves the next SOF inside the same word, more inserts idle words.
    """
    chance: int = 50
    max_bytes: int = 63


class MfbInputCoverage:
    """Positions of SOF and EOF of the accepted input words."""

    def __init__(self, dut: Any) -> None:
        self.dut = dut
        self.sof_pos: Counter = Counter()
        self.eof_pos: Counter = Counter()
        self.sof_eof_words = 0
        self.stall_cycles = 0
        cocotb.start_soon(self._run())

    async def _run(self) -> None:
        dut = self.dut
        while True:
            await RisingEdge(dut.CLK)
            if dut.RESET.value == 1 or dut.IN_MFB_SRC_RDY.value != 1:
                continue
            if dut.IN_MFB_DST_RDY.value != 1:
                self.stall_cycles += 1
                continue
            sof = dut.IN_MFB_SOF.value == 1
            eof = dut.IN_MFB_EOF.value == 1
            if sof:
                self.sof_pos[dut.IN_MFB_SOF_POS.value.to_unsigned()] += 1
            if eof:
                self.eof_pos[dut.IN_MFB_EOF_POS.value.to_unsigned()] += 1
            self.sof_eof_words += sof and eof


class Testbench:
    def __init__(self, dut: Any, idles: Optional[MfbIdles] = None) -> None:
        self.dut = dut
        if idles is None:
            self.mfb = MFBDriver(dut, "IN_MFB", dut.CLK, protocol=TxMfbProtocol, no_default_rate_limiter=True)
        else:
            # rate_percentage = 0: a random count of idle transactions (here 0 or 1) before each frame
            self.mfb = MFBDriver(dut, "IN_MFB", dut.CLK, protocol=TxMfbProtocol,
                                 idle_factory=IdleTransactionFactory(1, idles.max_bytes),
                                 rate_limiter_config=dict(rate_percentage=0, random_idles=True, max_idles=2,
                                                          zero_idles_chance=100 - idles.chance))
        self.saxis = SAXISMonitor(dut, "OUT_SAXIS", dut.CLK, reset=dut.RESET, callback=self._check_frame)
        self.checker = SAXISProtocolChecker(dut, "OUT_SAXIS", dut.CLK, reset=dut.RESET)
        self.in_cov = MfbInputCoverage(dut)

        self.expected: deque[bytes] = deque()
        self.sent = 0
        self.errors: list[str] = []

        dut.OUT_SAXIS_READY.value = 1
        dut.IN_MFB_SRC_RDY.value = 0

    def send(self, frame: bytes) -> None:
        self.expected.append(frame)
        self.sent += 1
        self.mfb.append(MfbTransaction(data=frame))

    def _check_frame(self, frame: bytes) -> None:
        index = self.saxis.frame_cnt - 1
        if not self.expected:
            self.errors.append(f"frame {index}: unexpected frame\n{format_bytes(frame, label='Received')}")
            return
        expected = self.expected.popleft()
        if frame != expected:
            self.errors.append(f"frame {index}: data mismatch (lengths {len(expected)} / {len(frame)})\n"
                               f"{format_bytes(expected, label='Expected')}\n{format_bytes(frame, label='Received')}")

    async def reset(self, cycles: int = 4) -> None:
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, cycles)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)

    async def wait_for_frames(self, count: int, timeout_cycles: int) -> None:
        for _ in range(timeout_cycles):
            if self.saxis.frame_cnt >= count:
                break
            await RisingEdge(self.dut.CLK)
        await ClockCycles(self.dut.CLK, 20)

    def check(self, frames: int) -> None:
        """Raises with a report of all problems found so far."""
        problems = list(self.errors)
        problems += self.checker.violations
        if self.saxis.frame_cnt != frames:
            problems.append(f"received {self.saxis.frame_cnt} frames, expected {frames}")
        if any(self.saxis.frame_err):
            problems.append(f"{sum(self.saxis.frame_err)} frames left with ERR = 1, the adapter never sets ERR")
        cocotb.log.info(self.checker.summary())
        cocotb.log.info(f"IN_MFB: SOF positions {dict(sorted(self.in_cov.sof_pos.items()))}, "
                        f"{len(self.in_cov.eof_pos)}/64 EOF positions, {self.in_cov.sof_eof_words} words with SOF and EOF, "
                        f"{self.in_cov.stall_cycles} cycles of IN_MFB_DST_RDY = 0")
        assert not problems, "Verification failed:\n" + "\n".join(problems[:20])
