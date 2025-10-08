# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 DynaNIC Semiconductors, Ltd.
# Author(s): Vlastimil Kosar <kosar@dyna-nic.com>

from collections import Counter
from dataclasses import dataclass, field
from typing import Any, Optional

import cocotb
from cocotb.triggers import ReadOnly, RisingEdge
from cocotb.utils import get_sim_time


@dataclass
class SAXISStatistics:
    """Coverage of the Segmented AXI-Stream traffic seen by :class:`SAXISProtocolChecker`."""
    cycles: int = 0
    transfers: int = 0
    stalls: int = 0
    frames: int = 0
    frames_err: int = 0
    used_segments: int = 0
    frame_gaps: int = 0
    sop_pos: Counter = field(default_factory=Counter)
    eop_pos: Counter = field(default_factory=Counter)
    mty: Counter = field(default_factory=Counter)
    eop_sop_cycles: int = 0
    stalls_in_frame: int = 0
    mty_without_eop: int = 0


class SAXISProtocolChecker:
    """Checks the placement rules of the Segmented AXI-Stream of PG369.

    The rules are those of "Transmit/Receive Segmented AXI4-Stream" and
    "Aborting a Transmission" of PG369:

    * a new SOP is in segment 0, a SOP in another segment directly follows an EOP
      in the previous segment of the same cycle,
    * between SOP and EOP all segments of a valid cycle are enabled,
    * no disabled segment between an EOP and a SOP, after the last EOP of a cycle
      only disabled segments follow,
    * SOP, EOP, ERR and a non-zero MTY only in enabled segments, ERR only with EOP,
    * a frame spans at least ``min_segments`` segments (EOP is not in the two
      segments after SOP),
    * with READY, the bus is stable while VALID is high and READY low.

    VALID low in the middle of a frame is counted in ``stats.frame_gaps``, it is
    a violation only with ``allow_frame_gaps=False``. A non-zero MTY in an
    enabled segment without EOP is counted in ``stats.mty_without_eop``, it is
    a violation only with ``strict_mty=True``; PG369 defines MTY for the EOP
    segment only.
    """

    def __init__(self, dut: Any, name: str, clock: Any, reset: Optional[Any] = None,
                 min_segments: int = 4, allow_frame_gaps: bool = True, strict_mty: bool = False,
                 max_violations: int = 50) -> None:
        self.name = name
        self.clock = clock
        self.reset = reset
        self.min_segments = min_segments
        self.allow_frame_gaps = allow_frame_gaps
        self.strict_mty = strict_mty
        self.max_violations = max_violations

        self.data = getattr(dut, f"{name}_DATA")
        self.mty_sig = getattr(dut, f"{name}_MTY")
        self.ena = getattr(dut, f"{name}_ENA")
        self.sop = getattr(dut, f"{name}_SOP")
        self.eop = getattr(dut, f"{name}_EOP")
        self.err = getattr(dut, f"{name}_ERR")
        self.valid = getattr(dut, f"{name}_VALID")
        self.ready = getattr(dut, f"{name}_READY", None)
        self.segments = len(self.sop)

        self.violations: list[str] = []
        self.stats = SAXISStatistics()
        self._in_frame = False
        self._frame_segments = 0
        self._stalled: Optional[tuple] = None
        cocotb.start_soon(self._run())

    def _violation(self, message: str) -> None:
        if len(self.violations) < self.max_violations:
            self.violations.append(f"{get_sim_time('ns'):.1f} ns: {self.name}: {message}")

    def _snapshot(self) -> tuple:
        return (int(self.valid.value), self.ena.value.to_unsigned(), self.sop.value.to_unsigned(),
                self.eop.value.to_unsigned(), self.err.value.to_unsigned(),
                tuple(self.mty_sig[i].value.to_unsigned() for i in range(self.segments)),
                tuple(self.data[i].value.to_unsigned() for i in range(self.segments)))

    async def _run(self) -> None:
        clk_re = RisingEdge(self.clock)
        read_only = ReadOnly()
        while True:
            # Sampled after all writes of this time step: drivers write some signals
            # immediately and others in ReadWrite, the edge itself shows a mix of
            # two cycles in some simulators (Questa).
            await clk_re
            await read_only
            if self.reset is not None and self.reset.value == 1:
                self._in_frame = False
                self._stalled = None
                continue

            self.stats.cycles += 1
            valid = self.valid.value == 1
            ready = self.ready is None or self.ready.value == 1

            if self._stalled is not None:
                if self._snapshot() != self._stalled:
                    self._violation("bus changed while VALID = 1 and READY = 0")

            if not valid:
                self._stalled = None
                if self._in_frame:
                    self.stats.frame_gaps += 1
                    if not self.allow_frame_gaps:
                        self._violation("VALID = 0 in the middle of a frame")
                continue

            if not ready:
                self.stats.stalls += 1
                if self._in_frame or self.sop.value.to_unsigned():
                    self.stats.stalls_in_frame += 1
                self._stalled = self._snapshot()
                continue

            self._stalled = None
            self.stats.transfers += 1
            self._check_cycle()

    def _check_cycle(self) -> None:
        ena = self.ena.value.to_unsigned()
        sop = self.sop.value.to_unsigned()
        eop = self.eop.value.to_unsigned()
        err = self.err.value.to_unsigned()

        if ena == 0:
            self._violation("VALID = 1 without an enabled segment")

        gap = False
        prev_eop = False
        had_eop = False
        for i in range(self.segments):
            bit = 1 << i
            mty = self.mty_sig[i].value.to_unsigned()

            if not ena & bit:
                if sop & bit or eop & bit or err & bit:
                    self._violation(f"SOP/EOP/ERR set in the disabled segment {i}")
                if self._in_frame:
                    self._violation(f"disabled segment {i} inside a frame")
                gap = True
                prev_eop = False
                continue

            if gap:
                self._violation(f"enabled segment {i} after a disabled segment")
            self.stats.used_segments += 1

            if sop & bit:
                if self._in_frame:
                    self._violation(f"SOP in segment {i} inside a frame")
                if i != 0 and not prev_eop:
                    self._violation(f"SOP in segment {i} does not follow an EOP in segment {i - 1}")
                if had_eop:
                    self.stats.eop_sop_cycles += 1
                self.stats.sop_pos[i] += 1
                self._in_frame = True
                self._frame_segments = 0
            elif not self._in_frame:
                self._violation(f"segment {i} enabled outside a frame")
                prev_eop = False
                continue

            self._frame_segments += 1

            if err & bit and not eop & bit:
                self._violation(f"ERR without EOP in segment {i}")
            if mty and not eop & bit:
                self.stats.mty_without_eop += 1
                if self.strict_mty:
                    self._violation(f"MTY = {mty} without EOP in segment {i}")

            prev_eop = bool(eop & bit)
            if prev_eop:
                if self._frame_segments < self.min_segments:
                    self._violation(f"frame of {self._frame_segments} segments ends in segment {i}, "
                                    f"at least {self.min_segments} are required")
                self.stats.frames += 1
                self.stats.frames_err += bool(err & bit)
                self.stats.eop_pos[i] += 1
                self.stats.mty[mty] += 1
                self._in_frame = False
                had_eop = True

    def summary(self) -> str:
        s = self.stats
        util = s.used_segments / max(1, s.transfers * self.segments)
        return (f"{self.name}: {s.frames} frames ({s.frames_err} with ERR), {s.transfers} transfers, "
                f"{s.stalls} stalls ({s.stalls_in_frame} in a frame), {s.frame_gaps} VALID gaps in frames, "
                f"segment utilization {100 * util:.1f} %, {s.eop_sop_cycles} cycles with EOP and SOP, "
                f"SOP positions {dict(sorted(s.sop_pos.items()))}, EOP positions {dict(sorted(s.eop_pos.items()))}, "
                f"MTY values {len(s.mty)}/16, {s.mty_without_eop} segments with MTY != 0 without EOP")
