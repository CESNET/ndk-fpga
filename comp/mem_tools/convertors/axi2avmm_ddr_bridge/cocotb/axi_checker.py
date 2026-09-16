# axi_checker.py: Passive AXI4 protocol checker for the DDR side of the bridge
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author: David Beneš <benes@dyna-nic.com>, 2026
#
# SPDX-License-Identifier: BSD-3-Clause

"""Passive AXI4 protocol checker for the DDR side of the bridge.

The checker only observes the bus, it never drives it. Besides reporting
protocol violations it also reconstructs the stream of accepted write beats
(byte address + data), which the scoreboard compares against the stream of
words the Avalon-MM master handed to the bridge.
"""

from dataclasses import dataclass, field
from typing import Any, Optional

import cocotb
from cocotb.triggers import ReadOnly, RisingEdge
from cocotb.utils import get_sim_time

from signals import bit, uint

# INCR is the only burst type the bridge is allowed to generate
AXI_BURST_INCR = 1


@dataclass
class AxiBurst:
    """One accepted AW/AR address phase."""
    address : int
    length  : int
    size    : int
    burst   : int
    axi_id  : int
    beats   : int = 0

    @property
    def bytes_per_beat(self) -> int:
        return 1 << self.size

    def beat_address(self, index: int) -> int:
        return self.address + index * self.bytes_per_beat


@dataclass
class WriteBeat:
    """One write data word as seen on the AXI W channel."""
    address : Optional[int]
    data    : bytes


@dataclass
class Violation:
    time    : str
    kind    : str
    message : str

    def __str__(self) -> str:
        return f"[{self.time}] {self.kind}: {self.message}"


@dataclass
class _ChannelSnapshot:
    """Values of one channel during the cycle that has just ended."""
    valid   : bool = False
    ready   : bool = False
    payload : tuple = field(default_factory=tuple)


class AxiProtocolChecker:
    def __init__(self, dut: Any, clock: Any, data_width: int, max_reports_per_kind: int = 5):
        self.dut = dut
        self.clock = clock
        self.log = cocotb.log

        self.bytes_per_word = data_width // 8

        # AxSIZE is log2 of the bytes per beat, which only means anything for a
        # power-of-two bus width.
        assert self.bytes_per_word & (self.bytes_per_word - 1) == 0, \
            f"data width must be a power of two, got {data_width} bits"
        self.expected_size = self.bytes_per_word.bit_length() - 1

        self.write_beats: list[WriteBeat] = []

        self._max_reports = max_reports_per_kind
        self._report_count: dict[str, int] = {}

        self._aw_queue: list[AxiBurst] = []
        self._ar_pending: list[AxiBurst] = []
        self._w_open: list[bytes] = []
        self._w_done: list[list[bytes]] = []
        self._w_overflow_reported: bool = False
        self._read_burst: Optional[AxiBurst] = None

        self._prev_aw = _ChannelSnapshot()
        self._prev_w  = _ChannelSnapshot()
        self._prev_ar = _ChannelSnapshot()

        self._enabled = False

        cocotb.start_soon(self._sample_loop())

    def enable(self, enabled: bool = True) -> None:
        self._enabled = enabled

    def _report(self, kind: str, message: str) -> None:
        count = self._report_count.get(kind, 0) + 1
        self._report_count[kind] = count

        if count > self._max_reports:
            return

        self.log.error("AXI protocol violation %s",
                       Violation(f"{get_sim_time('ns'):.0f} ns", kind, message))

        if count == self._max_reports:
            self.log.warning("Further '%s' reports will be counted but not printed", kind)

    def summary(self) -> str:
        if not self._report_count:
            return "no AXI protocol violations"

        rows = [f"{count:6d} x {kind}" for kind, count in sorted(self._report_count.items())]
        return "\n".join(rows)

    @property
    def violation_count(self) -> int:
        return sum(self._report_count.values())

    def _check_address_phase(self, name: str, burst: AxiBurst) -> None:
        if burst.size != self.expected_size:
            self._report(f"{name}SIZE", f"{name}SIZE={burst.size} but the data bus is {self.bytes_per_word} B wide (expected {self.expected_size})")

        if burst.burst != AXI_BURST_INCR:
            self._report(f"{name}BURST", f"{name}BURST={burst.burst:#04b}, only INCR ({AXI_BURST_INCR:#04b}) may be used")

        # the bridge is only ever built with USE_AXI_ID false
        if burst.axi_id != 0:
            self._report(f"{name}ID", f"{name}ID={burst.axi_id}, a single ID is required to keep responses ordered")

        if burst.address % burst.bytes_per_beat:
            self._report(f"{name}ADDR", f"{name}ADDR={burst.address:#x} is not aligned to the {burst.bytes_per_beat} B beat size")

    def _check_stability(self, name: str, prev: _ChannelSnapshot, valid: bool, payload: tuple) -> None:
        if not (prev.valid and not prev.ready):
            return

        if not valid:
            self._report(f"{name}_STABLE", f"{name}VALID was deasserted before {name}READY was received")
        elif payload != prev.payload:
            self._report(f"{name}_STABLE", f"{name} payload changed while {name}VALID was waiting for {name}READY: {prev.payload} -> {payload}")

    def _pair_write_bursts(self) -> None:
        """Matches finished write data bursts with their address phases.

        AXI4 allows the write data of a burst to be sent before its address
        phase, so the two streams are paired in order instead of expecting the
        address to come first.
        """
        while self._aw_queue and self._w_done:
            burst = self._aw_queue.pop(0)
            beats = self._w_done.pop(0)

            if len(beats) != burst.length + 1:
                self._report("WLAST", f"the burst at {burst.address:#x} announces AWLEN={burst.length} ({burst.length + 1} beats) but its write data ended after {len(beats)}")

            for index, data in enumerate(beats):
                self.write_beats.append(WriteBeat(burst.beat_address(index), data))

    def _handle_write_beat(self, data: bytes, last: bool) -> None:
        self._w_open.append(data)

        # Pairing keeps at most one of the two queues filled, so a waiting
        # address phase is the one belonging to the burst being received.
        announced = self._aw_queue[0].length if self._aw_queue and not self._w_done else None

        if announced is not None and len(self._w_open) > announced + 1 and not self._w_overflow_reported:
            self._report("WLAST", f"the burst at {self._aw_queue[0].address:#x} announces AWLEN={announced} ({announced + 1} beats) but already got {len(self._w_open)} beats without WLAST")
            self._w_overflow_reported = True

        if last:
            self._w_done.append(self._w_open)
            self._w_open = []
            self._w_overflow_reported = False
            self._pair_write_bursts()

    def finish(self) -> None:
        """Reports write bursts and address phases that stayed unmatched."""
        if self._w_open:
            self._report("WLAST", f"a write burst of {len(self._w_open)} beats never ended with WLAST")
            self._w_done.append(self._w_open)
            self._w_open = []
            self._pair_write_bursts()

        for beats in self._w_done:
            self._report("W_ORPHAN", f"a write burst of {len(beats)} beats was sent without a matching address phase")
            self.write_beats.extend(WriteBeat(None, data) for data in beats)

        self._w_done.clear()

        for burst in self._aw_queue:
            self._report("AW_ORPHAN", f"the address phase at {burst.address:#x} (AWLEN={burst.length}) never received its write data")

        self._aw_queue.clear()

    def _handle_read_beat(self, last: bool) -> None:
        if self._read_burst is None:
            if not self._ar_pending:
                self._report("R_ORPHAN", "read data beat accepted while no address phase is outstanding on the AR channel")
                return
            self._read_burst = self._ar_pending.pop(0)

        burst = self._read_burst
        burst.beats += 1

        if last:
            if burst.beats != burst.length + 1:
                self._report("RLAST", f"read burst at {burst.address:#x} (ARLEN={burst.length}) ended after {burst.beats} beats")
            self._read_burst = None

    async def _sample_loop(self) -> None:
        dut = self.dut
        strb_all_ones = "1" * self.bytes_per_word

        while True:
            # Same reason as in the Avalon-MM monitor, and here VALID comes from
            # the DUT while READY comes from a Python driver: only ReadOnly pins
            # both to the same cycle on every simulator.
            await RisingEdge(self.clock)
            await ReadOnly()

            if not self._enabled:
                continue

            aw_valid = bit(dut.DDR_S_AXI_AWVALID)
            aw_ready = bit(dut.DDR_S_AXI_AWREADY)
            w_valid  = bit(dut.DDR_S_AXI_WVALID)
            w_ready  = bit(dut.DDR_S_AXI_WREADY)
            ar_valid = bit(dut.DDR_S_AXI_ARVALID)
            ar_ready = bit(dut.DDR_S_AXI_ARREADY)
            r_valid  = bit(dut.DDR_S_AXI_RVALID)
            r_ready  = bit(dut.DDR_S_AXI_RREADY)

            aw_payload = (str(dut.DDR_S_AXI_AWADDR.value), str(dut.DDR_S_AXI_AWLEN.value),
                          str(dut.DDR_S_AXI_AWSIZE.value), str(dut.DDR_S_AXI_AWBURST.value),
                          str(dut.DDR_S_AXI_AWID.value))
            w_payload  = (str(dut.DDR_S_AXI_WDATA.value), str(dut.DDR_S_AXI_WSTRB.value),
                          str(dut.DDR_S_AXI_WLAST.value))
            ar_payload = (str(dut.DDR_S_AXI_ARADDR.value), str(dut.DDR_S_AXI_ARLEN.value),
                          str(dut.DDR_S_AXI_ARSIZE.value), str(dut.DDR_S_AXI_ARBURST.value),
                          str(dut.DDR_S_AXI_ARID.value))

            self._check_stability("AW", self._prev_aw, aw_valid, aw_payload)
            self._check_stability("W", self._prev_w, w_valid, w_payload)
            self._check_stability("AR", self._prev_ar, ar_valid, ar_payload)

            if aw_valid and aw_ready:
                fields = tuple(uint(sig) for sig in (dut.DDR_S_AXI_AWADDR, dut.DDR_S_AXI_AWLEN,
                                                     dut.DDR_S_AXI_AWSIZE, dut.DDR_S_AXI_AWBURST,
                                                     dut.DDR_S_AXI_AWID))
                if None in fields:
                    self._report("AW_UNKNOWN", f"AW address phase accepted with undefined bits: {aw_payload}")
                else:
                    burst = AxiBurst(*fields)
                    self._check_address_phase("AW", burst)
                    self._aw_queue.append(burst)
                    self._pair_write_bursts()

            if ar_valid and ar_ready:
                fields = tuple(uint(sig) for sig in (dut.DDR_S_AXI_ARADDR, dut.DDR_S_AXI_ARLEN,
                                                     dut.DDR_S_AXI_ARSIZE, dut.DDR_S_AXI_ARBURST,
                                                     dut.DDR_S_AXI_ARID))
                if None in fields:
                    self._report("AR_UNKNOWN", f"AR address phase accepted with undefined bits: {ar_payload}")
                else:
                    burst = AxiBurst(*fields)
                    self._check_address_phase("AR", burst)
                    self._ar_pending.append(burst)

            if w_valid and w_ready:
                strb = str(dut.DDR_S_AXI_WSTRB.value)
                if strb != strb_all_ones:
                    self._report("WSTRB", f"WSTRB={strb} but the bridge always writes whole words")

                data = uint(dut.DDR_S_AXI_WDATA)
                if data is None:
                    self._report("WDATA", "write data beat accepted with undefined bits")
                    data = 0

                self._handle_write_beat(data.to_bytes(self.bytes_per_word, "little"),
                                        bit(dut.DDR_S_AXI_WLAST))

            if r_valid and r_ready:
                self._handle_read_beat(bit(dut.DDR_S_AXI_RLAST))

            self._prev_aw = _ChannelSnapshot(aw_valid, aw_ready, aw_payload)
            self._prev_w  = _ChannelSnapshot(w_valid, w_ready, w_payload)
            self._prev_ar = _ChannelSnapshot(ar_valid, ar_ready, ar_payload)
