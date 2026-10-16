# testbench.py: Testbench infrastructure of the VERSAL_PS_CTRL verification
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2026
#
# SPDX-License-Identifier: BSD-3-Clause

"""Testbench of the Versal PS controller.

Agents:

* cocotbext-ofm ``MIRequestDriver`` drives the MI slave port (host software, CLK domain).
* cocotbext-axi ``AxiLiteMaster`` drives the AXI4-Lite slave port (BMC firmware on the PS).
* ``PsAxiSlave`` terminates the AXI4 master port (the PS) and checks its protocol.

Checkers:

* ``RegisterMonitor`` keeps a cycle accurate model of the register block. It
  observes the two MI buses at the inputs of the register block
  (``versal_ps_access_i.mi_int_*`` port 0 and ``mi_ps_*``), because the
  order of host and PS writes, including the priority of simultaneous writes,
  is defined there and cannot be reconstructed from the ports behind two clock
  domain crossings. The values read there are then compared with the values
  delivered on the external ports, so the external behaviour is still checked
  end to end.
* ``FpgaIdMonitor`` checks FPGA_ID / FPGA_ID_VLD against the DNA words the PS returned.
* The address window and the BUSY bit are checked at the ports only.
"""

import os
import random
from dataclasses import dataclass
from typing import Any, Optional

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import ClockCycles, RisingEdge, Timer
from cocotb.utils import get_sim_time
from cocotbext.axi import AxiLiteBus, AxiLiteMaster, AxiResp
from cocotbext.ofm.mi.drivers import MIRequestDriver

from model import (DNA_BASE, DNA_WORDS, LOWER_ADDR, STATUS, STATUS_ADDR64, STATUS_BUSY, UPPER_ADDR, WINDOW,
                   RegisterModel, fpga_id_from_words, window_address)
from ps_axi_slave import PsAxiSlave
from scoreboard import Scoreboard

# Polls of STATUS before a test gives up waiting for BUSY = 0.
BUSY_POLLS = 1000


def generic_int(dut: Any, name: str, env_default: str) -> int:
    """Value of an integer generic; the environment variable is the fallback for simulators without generic access."""
    try:
        return int(getattr(dut, name).value)
    except (AttributeError, TypeError, ValueError):
        return int(os.environ.get(f"VER_{name}", env_default), 0)


@dataclass
class HostAccess:
    write: bool
    offset: int
    data: int


@dataclass
class WindowOp:
    write: bool
    addr: int
    data: int = 0
    be: int = 0

    def __str__(self) -> str:
        if self.write:
            return f"W 0x{self.addr:x} data 0x{self.data:08x} strb 0x{self.be:x}"
        return f"R 0x{self.addr:x}"


class RegisterMonitor:
    """Cycle accurate model of the register block, see the module docstring."""

    def __init__(self, tb: "Testbench") -> None:
        self.tb = tb
        self.dut = tb.dut
        self.pa = tb.dut.versal_ps_access_i
        self.model = tb.regs
        self.violations: list[str] = []
        self.host_writes: list[tuple[int, int]] = []
        self.host_reads: list[int] = []
        self.ps_writes: list[tuple[int, int]] = []
        self.ps_reads: list[int] = []
        cocotb.start_soon(self._run())

    def clear(self) -> None:
        self.host_writes.clear()
        self.host_reads.clear()
        self.ps_writes.clear()
        self.ps_reads.clear()

    def _check(self, side: str, offset: int, actual: int, expected: int, mask: int = 0xFFFF_FFFF) -> None:
        if actual & mask != expected & mask:
            self.violations.append(f"{get_sim_time('ns'):.0f} ns: {side} read of offset 0x{offset & 0x7FF:03x} "
                                   f"returned 0x{actual:08x}, expected 0x{expected:08x} (mask 0x{mask:08x})")

    async def _run(self) -> None:
        while True:
            await RisingEdge(self.dut.AXI_LITE_CLK)

            host_write = None
            if int(self.pa.mi_int_rd.value[0]):
                offset = int(self.pa.mi_int_addr[0].value) & 0x7FF
                value = int(self.pa.mi_int_drd[0].value)
                # BUSY is time dependent, Testbench.status() checks it at the MI port.
                self._check("host", offset, value, self.model.host_read(offset),
                            ~STATUS_BUSY if offset == STATUS else 0xFFFF_FFFF)
                self.host_reads.append(value)
            if int(self.pa.mi_int_wr.value[0]):
                host_write = (int(self.pa.mi_int_addr[0].value) & 0x7FF, int(self.pa.mi_int_dwr[0].value))
                self.host_writes.append(host_write)

            ps_write = None
            if int(self.dut.mi_ps_rd.value):
                offset = int(self.dut.mi_ps_addr.value) & 0x7FF
                value = int(self.dut.mi_ps_drd.value)
                self._check("PS", offset, value, self.model.ps_read(offset))
                self.ps_reads.append(value)
            if int(self.dut.mi_ps_wr.value):
                ps_write = (int(self.dut.mi_ps_addr.value) & 0x7FF, int(self.dut.mi_ps_dwr.value))
                self.ps_writes.append(ps_write)

            self.model.write_cycle(host_write, ps_write)
            if int(self.dut.AXI_LITE_RESET.value):
                self.model.reset()


class FpgaIdMonitor:
    """Checks FPGA_ID_VLD and FPGA_ID in the CLK domain.

    After AXI_LITE_RESET the ID register is cleared and FPGA_ID follows a few
    cycles before FPGA_ID_VLD falls (the valid flag has a longer synchronizer).
    These changes are counted in ``reset_changes`` instead of being reported
    as violations.
    """

    def __init__(self, tb: "Testbench") -> None:
        self.tb = tb
        self.dut = tb.dut
        self.violations: list[str] = []
        self.rises: list[tuple[float, int]] = []
        self.reset_changes = 0
        # A previous test may have left FPGA_ID_VLD set, the testbench resets the DUT first.
        self.valid = bool(int(self.dut.FPGA_ID_VLD.value))
        cocotb.start_soon(self._run())

    async def _run(self) -> None:
        reset_since_rise = axil_reset_since_rise = True
        last_id = int(self.dut.FPGA_ID.value)
        while True:
            await RisingEdge(self.dut.CLK)
            now = get_sim_time("ns")
            if int(self.dut.AXI_LITE_RESET.value):
                axil_reset_since_rise = reset_since_rise = True
            if int(self.dut.RESET.value):
                reset_since_rise = True
            vld = bool(int(self.dut.FPGA_ID_VLD.value))
            fpga_id = int(self.dut.FPGA_ID.value)

            if vld and not self.valid:
                self.rises.append((now, fpga_id))
                self._check_rise(fpga_id)
                reset_since_rise = axil_reset_since_rise = False
            elif vld and fpga_id != last_id:
                if axil_reset_since_rise:
                    self.reset_changes += 1
                else:
                    self.violations.append(f"{now:.0f} ns: FPGA_ID changed while FPGA_ID_VLD = 1: "
                                           f"0x{last_id:032x} -> 0x{fpga_id:032x}")
            elif not vld and self.valid and not reset_since_rise:
                self.violations.append(f"{now:.0f} ns: FPGA_ID_VLD fell without a reset")

            self.valid = vld
            last_id = fpga_id

    def _check_rise(self, fpga_id: int) -> None:
        now = get_sim_time("ns")
        reads = self.tb.slave.id_reads(self.tb.slave.epoch)
        expected_addrs = [DNA_BASE + 4 * i for i in range(DNA_WORDS)]
        if [a.addr for a in reads] != expected_addrs or any(a.write for a in reads):
            self.violations.append(f"{now:.0f} ns: FPGA_ID_VLD set after the accesses {[str(a) for a in reads]}, "
                                   f"expected reads of {[hex(a) for a in expected_addrs]}")
            return
        if not all(a.completed for a in reads):
            self.violations.append(f"{now:.0f} ns: FPGA_ID_VLD set before the last DNA word was returned")
        expected = fpga_id_from_words([a.data for a in reads])
        if fpga_id != expected:
            self.violations.append(f"{now:.0f} ns: FPGA_ID 0x{fpga_id:032x}, expected 0x{expected:032x}")


class Testbench:
    def __init__(self, dut: Any, seed: int, clk_ps: int, axil_ps: int, mi_base: int) -> None:
        self.dut = dut
        self.log = cocotb.log
        self.rng = random.Random(seed)
        self.clk_ps = clk_ps
        self.axil_ps = axil_ps

        self.addr64 = generic_int(dut, "AXI_ADDR_WIDTH_INT", "32") == 64
        self.axi_addr_width = len(dut.AXI_AWADDR)
        self.read_smid = generic_int(dut, "READ_SMID", "1")
        self.write_smid = generic_int(dut, "WRITE_SMID", "1")

        self.slave = PsAxiSlave(dut, random.Random(self.rng.random()), self.read_smid, self.write_smid)
        # The DUT must decode only the lowest 12 address bits, the tests place it at a random base address.
        self.mi_base = mi_base
        self.host = MIRequestDriver(dut, "MI", dut.CLK)
        self.host_log: list[HostAccess] = []
        self.mi_violations: list[str] = []
        self.ps = AxiLiteMaster(AxiLiteBus.from_prefix(dut, "AXI_LITE"), dut.AXI_LITE_CLK, dut.AXI_LITE_RESET)
        self.regs = RegisterModel(self.addr64)
        # The BMC registers are not reset, they keep the values of the previous test.
        for name in self.regs.bmc:
            self.regs.bmc[name] = int(getattr(dut.versal_ps_access_i, f"bmc_{name}_reg").value)
        self.reg_monitor = RegisterMonitor(self)
        self.id_monitor = FpgaIdMonitor(self)
        cocotb.start_soon(self._mi_monitor())

        # The host software's view of the window registers and the expected window traffic
        self.upper = 0
        self.lower = 0
        self.expected_window: list[WindowOp] = []
        self.window_read_data: list[int] = []
        self.ps_log: list[tuple[bool, int, int, int]] = []
        self.status_errors: list[str] = []
        self.dna: list[int] = []

    # ------------------------------------------------------------------ control

    async def start_clocks(self) -> None:
        cocotb.start_soon(Clock(self.dut.CLK, self.clk_ps, unit="ps").start())
        # Random phase between the two domains
        await Timer(self.rng.randint(1, self.axil_ps - 1), unit="ps")
        cocotb.start_soon(Clock(self.dut.AXI_LITE_CLK, self.axil_ps, unit="ps").start())

    def load_dna(self, words: Optional[list[int]] = None) -> list[int]:
        """Content of the PMC eFUSE cache words read by VERSAL_FPGA_ID."""
        words = words if words is not None else [self.rng.getrandbits(32) for _ in range(DNA_WORDS)]
        for index, word in enumerate(words):
            self.slave.write_word(DNA_BASE + 4 * index, word)
        return words

    async def reset(self, host: bool = True, axi_lite: bool = True, cycles: int = 8) -> None:
        """Resets one or both clock domains; AXI_LITE_RESET also clears the window registers."""
        if host:
            self.dut.RESET.value = 1
        if axi_lite:
            self.dut.AXI_LITE_RESET.value = 1
        await ClockCycles(self.dut.CLK, cycles)
        await ClockCycles(self.dut.AXI_LITE_CLK, cycles)
        self.dut.RESET.value = 0
        self.dut.AXI_LITE_RESET.value = 0
        if axi_lite:
            self.upper = 0
            self.lower = 0
        await ClockCycles(self.dut.CLK, 2)

    async def wait_fpga_id(self, timeout_cycles: int = 5000) -> int:
        for _ in range(timeout_cycles):
            if int(self.dut.FPGA_ID_VLD.value):
                return int(self.dut.FPGA_ID.value)
            await RisingEdge(self.dut.CLK)
        raise AssertionError("FPGA_ID_VLD was not set")

    def restart_checks(self) -> None:
        """Forgets the recorded traffic, used after a reset in the middle of transactions."""
        self.host_log.clear()
        self.ps_log.clear()
        self.reg_monitor.clear()
        self.expected_window.clear()
        self.window_read_data.clear()
        self.slave.log.clear()

    # ------------------------------------------------------------------ host software

    async def _mi_monitor(self) -> None:
        pending_reads = 0
        while True:
            await RisingEdge(self.dut.CLK)
            if int(self.dut.MI_RD.value) and int(self.dut.MI_ARDY.value):
                pending_reads += 1
            if int(self.dut.MI_DRDY.value):
                if pending_reads == 0:
                    self.mi_violations.append(f"{get_sim_time('ns'):.0f} ns: MI_DRDY without a pending read")
                else:
                    pending_reads -= 1

    async def host_write(self, offset: int, data: int, be: int = 0xF) -> None:
        await self.host.write(self.mi_base + offset, data.to_bytes(4, "little"), byte_enable=be)
        self.host_log.append(HostAccess(True, offset, data))

    async def host_read(self, offset: int, be: int = 0xF) -> int:
        data = await self.host.read32(self.mi_base + offset, byte_enable=be)
        self.host_log.append(HostAccess(False, offset, data))
        return data

    async def status(self) -> int:
        """Reads STATUS and checks BUSY and ADDR64.

        BUSY = 0 means that every window access the host has issued is on the
        AXI bus; BUSY must be 0 when that was already true when the read was
        issued and the FPGA ID was valid.
        """
        id_valid = bool(int(self.dut.FPGA_ID_VLD.value))
        all_issued = len(self.slave.window_accesses) == len(self.expected_window)
        value = await self.host_read(STATUS)

        now = get_sim_time("ns")
        if value & ~(STATUS_BUSY | STATUS_ADDR64):
            self.status_errors.append(f"{now:.0f} ns: STATUS 0x{value:08x} has reserved bits set")
        if bool(value & STATUS_ADDR64) != self.addr64:
            self.status_errors.append(f"{now:.0f} ns: STATUS.ADDR64 = {value >> 1 & 1}, expected {int(self.addr64)}")
        if value & STATUS_BUSY and id_valid and all_issued:
            self.status_errors.append(f"{now:.0f} ns: STATUS.BUSY = 1 with no window access pending")
        if not value & STATUS_BUSY and len(self.slave.window_accesses) != len(self.expected_window):
            self.status_errors.append(f"{now:.0f} ns: STATUS.BUSY = 0, but only {len(self.slave.window_accesses)} "
                                      f"of {len(self.expected_window)} window accesses reached the AXI bus")
        return value

    async def wait_not_busy(self) -> None:
        for _ in range(BUSY_POLLS):
            if not await self.status() & STATUS_BUSY:
                return
        raise AssertionError(f"STATUS.BUSY did not clear after {BUSY_POLLS} polls")

    async def set_window(self, upper: int, lower: int) -> None:
        """Moves the window like the driver software does: only when no access is pending."""
        await self.wait_not_busy()
        await self.host_write(UPPER_ADDR, upper)
        await self.host_write(LOWER_ADDR, lower)
        self.upper, self.lower = upper, lower

    def window_target(self, offset: int) -> int:
        return window_address(self.upper, self.lower, WINDOW + offset, self.addr64, self.axi_addr_width)

    async def window_write(self, offset: int, data: int, be: int = 0xF) -> None:
        self.expected_window.append(WindowOp(True, self.window_target(offset), data, be))
        await self.host_write(WINDOW + offset, data, be)

    async def window_read(self, offset: int, be: int = 0xF) -> int:
        self.expected_window.append(WindowOp(False, self.window_target(offset)))
        value = await self.host_read(WINDOW + offset, be)
        self.window_read_data.append(value)
        return value

    # ------------------------------------------------------------------ BMC firmware

    async def ps_write(self, offset: int, data: int, length: int = 4) -> None:
        """Writes the lowest ``length`` bytes of ``data`` to the word aligned ``offset``."""
        data &= 2**(8 * length) - 1
        response = await self.ps.write(offset, data.to_bytes(length, "little"))
        self.ps_log.append((True, offset, data, int(response.resp)))

    async def ps_read(self, offset: int) -> int:
        response = await self.ps.read(offset & ~3, 4)
        value = int.from_bytes(response.data, "little")
        self.ps_log.append((False, offset, value, int(response.resp)))
        return value

    # ------------------------------------------------------------------ checks

    async def drain(self) -> None:
        """Waits until all host accesses reached the PS and the PS answered them."""
        await self.wait_not_busy()
        for _ in range(10000):
            if self.slave.outstanding == 0:
                break
            await RisingEdge(self.dut.AXI_LITE_CLK)
        await self.ps.wait()
        await ClockCycles(self.dut.AXI_LITE_CLK, 10)

    def check(self) -> Scoreboard:
        """Compares everything recorded so far and raises with a full report on any problem."""
        sb = Scoreboard()

        sb.add_errors("AXI4 master protocol", self.slave.violations)
        sb.add_errors("MI protocol", self.mi_violations)
        sb.add_errors("Register block", self.reg_monitor.violations)
        sb.add_errors("FPGA ID", self.id_monitor.violations)
        sb.add_errors("STATUS", self.status_errors)

        sb.compare_lists("Window accesses (MI request -> AXI)",
                         [str(op) for op in self.expected_window],
                         [str(WindowOp(a.write, a.addr, a.data, a.strb)) for a in self.slave.window_accesses])
        sb.compare_lists("Window read data (AXI RDATA -> MI_DRD)",
                         [f"0x{a.data:08x}" for a in self.slave.window_accesses if not a.write],
                         [f"0x{d:08x}" for d in self.window_read_data])
        sb.check(self.slave.outstanding == 0, f"{self.slave.outstanding} AXI transactions were not finished")

        host_regs = [a for a in self.host_log if a.offset & 0xFFF < WINDOW]
        sb.compare_lists("Host register writes (MI port -> register block)",
                         [f"0x{a.offset & 0x7FF:03x} 0x{a.data:08x}" for a in host_regs if a.write],
                         [f"0x{o:03x} 0x{d:08x}" for o, d in self.reg_monitor.host_writes])
        sb.compare_lists("Host register reads (register block -> MI port)",
                         [f"0x{d:08x}" for d in self.reg_monitor.host_reads],
                         [f"0x{a.data:08x}" for a in host_regs if not a.write])

        sb.compare_lists("PS writes (AXI4-Lite -> register block)",
                         [f"0x{o & 0x7FF:03x} 0x{d:08x}" for w, o, d, _ in self.ps_log if w],
                         [f"0x{o:03x} 0x{d:08x}" for o, d in self.reg_monitor.ps_writes])
        sb.compare_lists("PS reads (register block -> AXI4-Lite)",
                         [f"0x{d:08x}" for d in self.reg_monitor.ps_reads],
                         [f"0x{d:08x}" for w, _, d, _ in self.ps_log if not w])
        sb.compare_lists("AXI4-Lite responses",
                         [AxiResp.OKAY.value] * len(self.ps_log), [r for _, _, _, r in self.ps_log])

        if self.id_monitor.reset_changes:
            self.log.warning("FPGA_ID changed %d times while FPGA_ID_VLD = 1 after AXI_LITE_RESET",
                             self.id_monitor.reset_changes)
        self.log.info("Checked %d window accesses, %d host and %d PS register accesses, %d FPGA ID updates",
                      len(self.expected_window), len(host_regs), len(self.ps_log), len(self.id_monitor.rises))
        sb.result()
        return sb


async def get_testbench(dut: Any, seed: int = 0, clk_ps: int = 5000, axil_ps: int = 8000,
                        mi_base: Optional[int] = None, dna: Optional[list[int]] = None,
                        wait_id: bool = True) -> Testbench:
    """Builds a testbench for one test, resets the DUT and by default waits for the FPGA ID."""
    dut.RESET.value = 1
    dut.AXI_LITE_RESET.value = 1

    rng = random.Random(seed)
    base = mi_base if mi_base is not None else rng.getrandbits(20) << 12
    tb = Testbench(dut, seed, clk_ps, axil_ps, base)
    tb.dna = tb.load_dna(dna)
    await tb.start_clocks()
    await tb.reset()
    if wait_id:
        await tb.wait_fpga_id()
    return tb
