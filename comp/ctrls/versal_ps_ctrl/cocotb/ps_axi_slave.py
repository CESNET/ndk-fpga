# ps_axi_slave.py: Model of the PS AXI4 slave port for the VERSAL_PS_CTRL verification
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2026
#
# SPDX-License-Identifier: BSD-3-Clause

"""AXI4 slave standing in for the PS, with a protocol checker of the DUT master.

Each access is tagged with the internal FPGA ID valid flag (the select of
VERSAL_AXI_SWITCH), which tells the FPGA ID reads from the window accesses.

cocotbext-axi's AxiRam is not used: it cannot return error responses, cannot
hold the address channels or the responses on request, and its memory is a
flat buffer that cannot cover a 49 or 64-bit address space. The DUT issues
single-beat transfers only, so a dedicated model stays small.
"""

import hashlib
import random
from dataclasses import dataclass
from typing import Any, Callable, Optional

import cocotb
from cocotb.triggers import RisingEdge
from cocotb.utils import get_sim_time

OKAY, EXOKAY, SLVERR, DECERR = 0, 1, 2, 3

# (signal suffix, expected value or None) of the address channel sideband;
# USER and ID are checked separately, the widths depend on generics.
ADDR_SIDEBAND = (("LEN", 0), ("SIZE", 2), ("BURST", 1), ("PROT", 0), ("CACHE", 0), ("LOCK", 0), ("QOS", 0))


def default_word(addr: int) -> int:
    """Content of a word that has never been written, unique for every address."""
    return int.from_bytes(hashlib.blake2b(addr.to_bytes(8, "little"), digest_size=4).digest(), "little")


@dataclass
class AxiAccess:
    """One completed or pending AXI transaction as seen on the master port."""
    write: bool
    addr: int
    data: int = 0
    strb: int = 0
    resp: int = OKAY
    user: int = 0
    id_done: bool = True
    epoch: int = 0
    time_ns: float = 0.0
    completed: bool = False

    def __str__(self) -> str:
        if self.write:
            return f"W 0x{self.addr:x} data 0x{self.data:08x} strb 0x{self.strb:x} resp {self.resp}"
        return f"R 0x{self.addr:x} data 0x{self.data:08x} resp {self.resp}"


class _Channel:
    """Valid/ready channel of the DUT master: handshake detection and stability check."""

    def __init__(self, slave: "PsAxiSlave", name: str, payload: list[str]) -> None:
        self.slave = slave
        self.name = name
        self.valid = getattr(slave.dut, f"AXI_{name}VALID")
        self.ready = getattr(slave.dut, f"AXI_{name}READY")
        self.payload = [(sig, getattr(slave.dut, f"AXI_{sig}")) for sig in payload]
        self.waiting: Optional[dict[str, int]] = None
        self.ready_rate = 1.0
        self.hold = False

    def sample(self) -> Optional[dict[str, int]]:
        """Returns the payload on a handshake in this cycle, checks the AXI stability rule otherwise."""
        valid = int(self.valid.value)
        values = {sig: int(handle.value) for sig, handle in self.payload} if valid else {}

        if self.waiting is not None:
            if not valid:
                self.slave.violation(f"{self.name}VALID dropped before the handshake")
            elif values != self.waiting:
                self.slave.violation(f"{self.name} payload changed while waiting for {self.name}READY: "
                                     f"{self.waiting} -> {values}")

        if valid and int(self.ready.value):
            self.waiting = None
            return values

        self.waiting = values if valid else None
        return None

    def drive_ready(self) -> None:
        self.ready.value = int(not self.hold and self.slave.rng.random() < self.ready_rate)

    def reset(self) -> None:
        self.waiting = None
        self.ready.value = 0


class PsAxiSlave:
    """PS side of the AXI4 master port: sparse memory, configurable timing and responses.

    Every transaction is logged in ``log``; protocol violations of the DUT are
    collected in ``violations``. The model does not assume a single
    outstanding transaction, it only reports it as a violation.
    """

    def __init__(self, dut: Any, rng: random.Random, read_smid: int, write_smid: int) -> None:
        self.dut = dut
        self.clk = dut.AXI_LITE_CLK
        self.rst = dut.AXI_LITE_RESET
        self.rng = rng
        self.read_smid = read_smid
        self.write_smid = write_smid
        self.id_width = len(dut.AXI_AWID)

        self.memory: dict[int, int] = {}
        self.log: list[AxiAccess] = []
        self.violations: list[str] = []
        # Incremented by every AXI_LITE_RESET, separates the FPGA ID reads of successive resets.
        self.epoch = 0
        self._in_reset = False

        self.latency = (0, 0)
        self.resp_fn: Callable[[bool, int], int] = lambda write, addr: OKAY
        self.hold_responses = False

        self.aw = _Channel(self, "AW", ["AWADDR", "AWID", "AWUSER", "AWLEN", "AWSIZE", "AWBURST",
                                        "AWPROT", "AWCACHE", "AWLOCK", "AWQOS"])
        self.w = _Channel(self, "W", ["WDATA", "WSTRB", "WLAST"])
        self.ar = _Channel(self, "AR", ["ARADDR", "ARID", "ARUSER", "ARLEN", "ARSIZE", "ARBURST",
                                        "ARPROT", "ARCACHE", "ARLOCK", "ARQOS"])

        self._clear()
        cocotb.start_soon(self._run())

    # ------------------------------------------------------------------ setup

    def set_ready_rates(self, aw: float = 1.0, w: float = 1.0, ar: float = 1.0) -> None:
        """Probability of READY being high in a cycle for each request channel."""
        self.aw.ready_rate, self.w.ready_rate, self.ar.ready_rate = aw, w, ar

    def set_latency(self, minimum: int, maximum: int) -> None:
        """Cycles between the request (both AW and W for writes) and the B/R response."""
        self.latency = (minimum, maximum)

    def set_response(self, resp: int) -> None:
        """Answers every following transaction with ``resp``."""
        self.resp_fn = lambda write, addr: resp

    def hold_address(self, hold: bool) -> None:
        """Keeps AWREADY and ARREADY low, the DUT then waits with its address."""
        self.aw.hold = self.ar.hold = hold

    def read_word(self, addr: int) -> int:
        return self.memory.get(addr & ~3, default_word(addr & ~3))

    def write_word(self, addr: int, data: int, strb: int = 0xF) -> None:
        word = self.read_word(addr)
        for byte in range(4):
            if strb >> byte & 1:
                mask = 0xFF << (8 * byte)
                word = (word & ~mask) | (data & mask)
        self.memory[addr & ~3] = word

    # ------------------------------------------------------------------ queries

    def violation(self, message: str) -> None:
        self.violations.append(f"{get_sim_time('ns'):.0f} ns: {message}")

    @property
    def window_accesses(self) -> list[AxiAccess]:
        return [a for a in self.log if a.id_done]

    def id_reads(self, epoch: int) -> list[AxiAccess]:
        """Accesses made while the FPGA ID was not valid yet (the AXI switch selects VERSAL_FPGA_ID)."""
        return [a for a in self.log if not a.id_done and a.epoch == epoch]

    @property
    def outstanding(self) -> int:
        return sum(1 for a in self.log if not a.completed)

    # ------------------------------------------------------------------ model

    def _clear(self) -> None:
        self.pending_aw: list[AxiAccess] = []
        self.pending_w: list[tuple[int, int]] = []
        self.b_queue: list[tuple[int, AxiAccess]] = []
        self.r_queue: list[tuple[int, AxiAccess]] = []
        self.b_active: Optional[AxiAccess] = None
        self.r_active: Optional[AxiAccess] = None
        self.cycle = 0
        for channel in (self.aw, self.w, self.ar):
            channel.reset()
        self.dut.AXI_BVALID.value = 0
        self.dut.AXI_RVALID.value = 0
        self.dut.AXI_BID.value = 0
        self.dut.AXI_RID.value = 0
        self.dut.AXI_BRESP.value = 0
        self.dut.AXI_RRESP.value = 0
        self.dut.AXI_RDATA.value = 0
        self.dut.AXI_RLAST.value = 0

    def _check_request(self, kind: str, values: dict[str, int], smid: int) -> None:
        for sig, expected in ADDR_SIDEBAND:
            if values[kind + sig] != expected:
                self.violation(f"{kind}{sig} = {values[kind + sig]}, expected {expected}")
        if values[kind + "ID"] != 0:
            self.violation(f"{kind}ID = {values[kind + 'ID']}, expected 0")
        if values[kind + "USER"] != smid:
            self.violation(f"{kind}USER = 0x{values[kind + 'USER']:x}, expected SMID 0x{smid:x}")
        if values[kind + "ADDR"] & 3:
            self.violation(f"{kind}ADDR 0x{values[kind + 'ADDR']:x} is not word aligned")
        if self.outstanding:
            self.violation(f"{kind} request while {self.outstanding} transaction(s) are not finished")

    def _new_access(self, write: bool, values: dict[str, int]) -> AxiAccess:
        kind = "AW" if write else "AR"
        self._check_request(kind, values, self.write_smid if write else self.read_smid)
        access = AxiAccess(write=write, addr=values[kind + "ADDR"], user=values[kind + "USER"],
                           id_done=bool(int(self.dut.fpga_id_int_vld.value)), epoch=self.epoch,
                           time_ns=get_sim_time("ns"))
        self.log.append(access)
        return access

    def _response_time(self) -> int:
        return self.cycle + self.rng.randint(*self.latency)

    def _run_cycle(self) -> None:
        if self.b_active is not None and int(self.dut.AXI_BREADY.value):
            self.b_active.completed = True
            self.b_active = None
        if self.r_active is not None and int(self.dut.AXI_RREADY.value):
            self.r_active.completed = True
            self.r_active = None

        aw = self.aw.sample()
        w = self.w.sample()
        ar = self.ar.sample()

        if aw is not None:
            self.pending_aw.append(self._new_access(True, aw))
        if w is not None:
            if w["WLAST"] != 1:
                self.violation("WLAST = 0 on a single-beat write")
            self.pending_w.append((w["WDATA"], w["WSTRB"]))
        while self.pending_aw and self.pending_w:
            access = self.pending_aw.pop(0)
            access.data, access.strb = self.pending_w.pop(0)
            access.resp = self.resp_fn(True, access.addr)
            if access.resp in (OKAY, EXOKAY):
                self.write_word(access.addr, access.data, access.strb)
            self.b_queue.append((self._response_time(), access))
        if ar is not None:
            access = self._new_access(False, ar)
            access.resp = self.resp_fn(False, access.addr)
            access.data = self.read_word(access.addr)
            self.r_queue.append((self._response_time(), access))

        if not self.hold_responses:
            if self.b_active is None and self.b_queue and self.b_queue[0][0] <= self.cycle:
                self.b_active = self.b_queue.pop(0)[1]
            if self.r_active is None and self.r_queue and self.r_queue[0][0] <= self.cycle:
                self.r_active = self.r_queue.pop(0)[1]

        self.dut.AXI_BVALID.value = int(self.b_active is not None)
        self.dut.AXI_BRESP.value = self.b_active.resp if self.b_active else 0
        self.dut.AXI_BID.value = 0
        self.dut.AXI_RVALID.value = int(self.r_active is not None)
        self.dut.AXI_RRESP.value = self.r_active.resp if self.r_active else 0
        self.dut.AXI_RDATA.value = self.r_active.data if self.r_active else 0
        self.dut.AXI_RLAST.value = int(self.r_active is not None)
        self.dut.AXI_RID.value = 0

        for channel in (self.aw, self.w, self.ar):
            channel.drive_ready()

    async def _run(self) -> None:
        while True:
            await RisingEdge(self.clk)
            if int(self.rst.value):
                # The PS port is reset together with the DUT, unfinished transactions are dropped.
                if not self._in_reset:
                    self.epoch += 1
                    self._in_reset = True
                for access in self.log:
                    access.completed = True
                self._clear()
                continue
            self._in_reset = False
            self.cycle += 1
            self._run_cycle()
