# testbench.py: Testbench of the RX_MAC_LITE_ADAPTER_SAXIS verification
# Copyright (C) 2026 DynaNIC Semiconductors, Ltd.
# Author(s): Vlastimil Kosar <kosar@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

"""Segmented AXI-Stream driver -> RX_MAC_LITE_ADAPTER_SAXIS -> MFB monitor.

The reference model is the identity: every frame leaves in order and
unchanged, OUT_MFB_ERROR is set with the EOF of the frames that had ERR in
their EOP segment. The protocol checker on the input confirms that the
stimulus follows PG369 (or counts where it intentionally does not).
"""

from collections import deque
from typing import Any

import cocotb
from cocotb.triggers import ClockCycles, RisingEdge
from cocotbext.ofm.base.generators import IdleGenerator, ItemRateLimiter
from cocotbext.ofm.mfb.monitors import MFBMonitor
from cocotbext.ofm.saxis.checker import SAXISProtocolChecker
from cocotbext.ofm.saxis.drivers import SAXISDriver
from cocotbext.ofm.utils.hex_formatter import format_bytes


class Testbench:
    def __init__(self, dut: Any, idle_mode: str = "cycle", rate_percentage: int = 0,
                 inner_gap_prob: float = 0.0, min_segments: int = 4) -> None:
        self.dut = dut
        self.segments = len(dut.IN_SAXIS_SOP)
        self.saxis = SAXISDriver(dut, "IN_SAXIS", dut.CLK, idle_mode=idle_mode, inner_gap_prob=inner_gap_prob)
        if rate_percentage:
            self.saxis.set_idle_generator(ItemRateLimiter(rate_percentage=rate_percentage, random_idles=True))
        else:
            self.saxis.set_idle_generator(IdleGenerator())
        self.checker = SAXISProtocolChecker(dut, "IN_SAXIS", dut.CLK, reset=dut.RESET, min_segments=min_segments)
        self.mfb = MFBMonitor(dut, "OUT_MFB", dut.CLK)
        self.mfb.add_callback(self._check_frame)

        self.expected: deque[bytes] = deque()
        self.expected_errors: list[bool] = []
        self.mfb_errors: list[bool] = []
        self.errors: list[str] = []
        self.received = 0
        cocotb.start_soon(self._error_monitor())

    def send(self, frame: bytes, err: bool = False) -> None:
        self.expected.append(frame)
        self.expected_errors.append(err)
        self.saxis.append(frame, err=err)

    async def _error_monitor(self) -> None:
        dut = self.dut
        while True:
            await RisingEdge(dut.CLK)
            if dut.OUT_MFB_SRC_RDY.value == 1 and dut.OUT_MFB_EOF.value == 1:
                self.mfb_errors.append(dut.OUT_MFB_ERROR.value == 1)

    def _check_frame(self, frame: bytes) -> None:
        index = self.received
        self.received += 1
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
            if self.received >= count:
                break
            await RisingEdge(self.dut.CLK)
        await ClockCycles(self.dut.CLK, 10)

    def check(self, frames: int, compliant: bool = True) -> None:
        """Raises with a report of all problems found so far.

        ``compliant=False`` accepts the PG369 violations of the stimulus that
        the test produces on purpose.
        """
        problems = list(self.errors)
        if compliant:
            problems += [f"stimulus: {v}" for v in self.checker.violations]
        if self.received != frames:
            problems.append(f"received {self.received} frames, expected {frames}")
        if len(self.mfb_errors) != frames:
            problems.append(f"{len(self.mfb_errors)} EOFs seen, expected {frames}")
        wrong_err = [i for i, (a, e) in enumerate(zip(self.mfb_errors, self.expected_errors)) if a != e]
        if wrong_err:
            problems.append(f"OUT_MFB_ERROR differs from the input ERR in {len(wrong_err)} frames, first {wrong_err[:10]}")
        cocotb.log.info(self.checker.summary())
        cocotb.log.info(f"OUT_MFB: {self.mfb.frame_cnt} frames, {sum(self.mfb_errors)} with OUT_MFB_ERROR")
        assert not problems, "Verification failed:\n" + "\n".join(problems[:20])
