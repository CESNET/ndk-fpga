# axil_checker.py: AXI4-Lite slave port checker of the AXI4LITE2MI verification
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2026
#
# SPDX-License-Identifier: BSD-3-Clause

"""Passive observer of the AXI4-Lite slave port of the DUT.

It records every handshake for the scoreboard and checks the rules of the AXI
specification that apply to a slave, together with the behaviour the component
documents: one transaction at a time, reads served before writes, WREADY only
after the write address handshake and OKAY responses only.
"""

from dataclasses import dataclass
from typing import Any, Optional

import cocotb
from cocotb.triggers import RisingEdge


@dataclass
class Handshake:
    cycle : int
    addr  : int = 0
    data  : int = 0
    strb  : int = 0
    resp  : int = 0


class AxiLiteSlaveChecker:
    MAX_REPORTED = 20

    def __init__(self, dut: Any, clock: Any) -> None:
        self.dut = dut
        self.clock = clock
        self.log = cocotb.log.getChild("axil_checker")

        self.enabled = False
        self.cycle = 0

        self.aw: list[Handshake] = []
        self.w: list[Handshake] = []
        self.b: list[Handshake] = []
        self.ar: list[Handshake] = []
        self.r: list[Handshake] = []

        self.violations: list[str] = []
        self.violation_count = 0

        self._r_hold: Optional[tuple[str, str]] = None  # (RDATA, RRESP) of an RVALID not yet accepted
        self._b_hold: Optional[str] = None

        cocotb.start_soon(self._run())

    def enable(self, value: bool) -> None:
        if value:
            self.clear()
        self.enabled = value

    def clear(self) -> None:
        for queue in (self.aw, self.w, self.b, self.ar, self.r):
            queue.clear()
        self.violations.clear()
        self.violation_count = 0
        self._r_hold = None
        self._b_hold = None

    @property
    def reads_in_flight(self) -> int:
        return len(self.ar) - len(self.r)

    @property
    def writes_in_flight(self) -> int:
        return len(self.aw) - len(self.b)

    def _violation(self, message: str) -> None:
        self.violation_count += 1
        if len(self.violations) < self.MAX_REPORTED:
            text = f"cycle {self.cycle}: {message}"
            self.violations.append(text)
            self.log.error("AXI4-Lite: %s", text)

    @staticmethod
    def _bit(signal: Any) -> bool:
        value = signal.value
        return value.is_resolvable and bool(value)

    async def _run(self) -> None:
        edge = RisingEdge(self.clock)

        while True:
            await edge
            self.cycle += 1

            if not self.enabled:
                continue

            dut = self.dut

            if self._bit(dut.RESET):
                self._r_hold = None
                self._b_hold = None
                if self._bit(dut.AXI_RVALID) or self._bit(dut.AXI_BVALID):
                    self._violation("RVALID or BVALID asserted during reset")
                continue

            self._check_cycle(dut)

    def _check_cycle(self, dut: Any) -> None:
        for name in ("AXI_AWREADY", "AXI_WREADY", "AXI_BVALID", "AXI_ARREADY", "AXI_RVALID"):
            if not getattr(dut, name).value.is_resolvable:
                self._violation(f"{name} is not resolvable: {getattr(dut, name).value}")

        awvalid, awready = self._bit(dut.AXI_AWVALID), self._bit(dut.AXI_AWREADY)
        wvalid, wready = self._bit(dut.AXI_WVALID), self._bit(dut.AXI_WREADY)
        bvalid, bready = self._bit(dut.AXI_BVALID), self._bit(dut.AXI_BREADY)
        arvalid, arready = self._bit(dut.AXI_ARVALID), self._bit(dut.AXI_ARREADY)
        rvalid, rready = self._bit(dut.AXI_RVALID), self._bit(dut.AXI_RREADY)

        # --- documented behaviour of the component ---------------------------
        if arready and awready:
            self._violation("ARREADY and AWREADY asserted in the same cycle")
        if awready and arvalid:
            self._violation("write address accepted while a read address was pending (reads have priority)")
        if (arready or awready) and (self.reads_in_flight or self.writes_in_flight):
            self._violation("new address accepted while a transaction is in flight")
        if wready and len(self.w) >= len(self.aw):
            self._violation("WREADY asserted before the write address was accepted")

        # --- responses ---------------------------------------------------------
        if rvalid:
            rdata, rresp = dut.AXI_RDATA.value, dut.AXI_RRESP.value
            if not (rdata.is_resolvable and rresp.is_resolvable):
                self._violation(f"RDATA/RRESP not resolvable with RVALID: {rdata}/{rresp}")
            current = (str(rdata), str(rresp))
            if self._r_hold is not None and self._r_hold != current:
                self._violation(f"RDATA/RRESP changed while waiting for RREADY: {self._r_hold} -> {current}")
            if self.reads_in_flight <= 0:
                self._violation("RVALID without an outstanding read")
            if rready:
                resp = rresp.to_unsigned() if rresp.is_resolvable else -1
                self.r.append(Handshake(self.cycle, data=rdata.to_unsigned() if rdata.is_resolvable else 0, resp=resp))
                self._r_hold = None
            else:
                self._r_hold = current
        elif self._r_hold is not None:
            self._violation("RVALID deasserted before RREADY")
            self._r_hold = None

        if bvalid:
            bresp = dut.AXI_BRESP.value
            if not bresp.is_resolvable:
                self._violation(f"BRESP not resolvable with BVALID: {bresp}")
            current_b = str(bresp)
            if self._b_hold is not None and self._b_hold != current_b:
                self._violation(f"BRESP changed while waiting for BREADY: {self._b_hold} -> {current_b}")
            if self.writes_in_flight <= 0 or len(self.w) < len(self.aw):
                self._violation("BVALID before both the write address and data were accepted")
            if bready:
                self.b.append(Handshake(self.cycle, resp=bresp.to_unsigned() if bresp.is_resolvable else -1))
                self._b_hold = None
            else:
                self._b_hold = current_b
        elif self._b_hold is not None:
            self._violation("BVALID deasserted before BREADY")
            self._b_hold = None

        # --- requests (recorded after the response checks of this cycle) --------
        if arvalid and arready:
            self.ar.append(Handshake(self.cycle, addr=dut.AXI_ARADDR.value.to_unsigned()))
        if awvalid and awready:
            self.aw.append(Handshake(self.cycle, addr=dut.AXI_AWADDR.value.to_unsigned()))
        if wvalid and wready:
            self.w.append(Handshake(self.cycle, data=dut.AXI_WDATA.value.to_unsigned(),
                                    strb=dut.AXI_WSTRB.value.to_unsigned()))

    def finish(self) -> None:
        if self.reads_in_flight or self.writes_in_flight:
            self._violation(f"transactions still in flight at the end: {self.reads_in_flight} reads, "
                            f"{self.writes_in_flight} writes")
