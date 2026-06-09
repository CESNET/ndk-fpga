# cocotb_test.py:
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import itertools

import cocotb
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb_bus.drivers import BitDriver
from cocotb_bus.scoreboard import Scoreboard

from cocotbext.ofm.utils import RAM
from cocotbext.ofm.mvb.transaction import MvbTrClassic
from cocotbext.ofm.mvb.monitors import MVBMonitor
from cocotbext.ofm.base.generators import ItemRateLimiter
from cocotbext.ofm.ver.generators import random_packets

from transaction import PprInstr, PprData
from drivers import PprDriver, PcieDriver
from monitors import PprMonitor
from responder import PprRequester
from addr_tracker import AddressRangeTracker


def _format_packet_bytes(packet_bytes: bytes, label: str) -> str:
    """Format packet bytes for display, 16 bytes per line."""
    lines = [f"{label}:"]
    for i in range(0, len(packet_bytes), 16):
        chunk = packet_bytes[i:i+16]
        hex_str = ' '.join(f'{b:02X}' for b in chunk)
        lines.append(f"  {i:04X}: {hex_str:<48}")
    return '\n'.join(lines)


def _compare_transactions(expected: PprData, actual: PprData, packet_num: int = 0) -> tuple:
    """Compare two PprData transactions with detailed mismatch output."""
    match = (expected.data == actual.data) and (expected.id == actual.id)

    if match:
        return True, ""

    lines = []
    lines.append("")
    lines.append("#" + "=" * 78 + "#")
    lines.append("#" + " " * 25 + f"PACKET MISMATCH #{packet_num}" + " " * (36-len(str(packet_num))) + "#")
    lines.append("#" + "=" * 78 + "#")
    lines.append(f"#  Expected ID: {expected.id}")
    lines.append(f"#  Actual ID:   {actual.id}")
    lines.append(f"#  Expected length: {len(expected.data):>5} bytes")
    lines.append(f"#  Actual length:   {len(actual.data):>5} bytes")
    lines.append("#" + "=" * 78 + "#")
    lines.append("")

    msg = "\n".join(lines)

    if hasattr(expected, 'data') and expected.data:
        msg += "\n" + _format_packet_bytes(expected.data, "Expected data bytes") + "\n"
    if hasattr(actual, 'data') and actual.data:
        msg += "\n" + _format_packet_bytes(actual.data, "Actual data bytes") + "\n"

    # Find first difference
    if expected.data != actual.data:
        min_len = min(len(expected.data), len(actual.data))
        for i in range(min_len):
            if expected.data[i] != actual.data[i]:
                msg += f"\nFirst difference at byte {i}:"
                msg += f"\n  Expected: 0x{expected.data[i]:02X}"
                msg += f"\n  Actual:   0x{actual.data[i]:02X}"
                break
        else:
            if len(expected.data) != len(actual.data):
                msg += f"\nLength mismatch: expected {len(expected.data)} bytes, got {len(actual.data)} bytes"

    return False, msg


class Testbench():
    def __init__(self, dut, debug=False, **kwargs):
        self.dut = dut
        self.user_req_drv = PprDriver(dut, "USER_REQ_MVB", dut.CLK)
        self.pcie_up_drv = BitDriver(dut.PCIE_UP_MVB_DST_RDY, dut.CLK)
        self.pcie_up_mon = MVBMonitor(dut, "PCIE_UP_MVB", dut.CLK, tr_type=MvbTrClassic)
        self.pcie_down_drv = PcieDriver(dut, "PCIE_DOWN", dut.CLK)
        self.user_resp_mon = PprMonitor(dut, "USER_RESP_MFB", dut.CLK)
        self.user_resp_drv = BitDriver(dut.USER_RESP_MFB_DST_RDY, dut.CLK)

        self.ram_capacity = 0x08000000
        self.ram = RAM(self.ram_capacity)
        # PCIe responder to create responses from requests
        self.requester = PprRequester(
            ram=self.ram,
            rq_driver=self.pcie_up_drv,
            rc_driver=self.pcie_down_drv,
            rq_monitor=self.pcie_up_mon,
            mps=kwargs.get("mps", 256),
            rcb=kwargs.get("rcb", 64),
            cpl_split_mode=kwargs.get("cpl_split_mode", 2),
            cpl_dly=kwargs.get("cpl_dly", 10)
        )
        # Address tracker to prevent overlapping memory accesses
        self.addr_tracker = AddressRangeTracker(self.ram_capacity)
        self.exp_output = []
        self.packets_expected = kwargs.get("pkts_exp", 10000)
        self.packets_received = 0
        # Track which IDs are currently in use (not yet received)
        self.ids_in_use = set()
        # Read the RESP_IN_ORDER generic from the DUT to determine output ordering
        self.resp_in_order = bool(dut.RESP_IN_ORDER.value)

        self.scoreboard = Scoreboard(dut)

        def compare_wrapper(actual):
            """
            Compare actual output with expected, providing detailed mismatch info.
            Supports in-order and out-of-order response checking based on self.resp_in_order.
            """
            if not self.exp_output:
                cocotb.log.error("Received unexpected packet")
                return

            if self.resp_in_order:
                # In-order mode: response must match the oldest expected packet
                if actual.id != self.exp_output[0].id:
                    cocotb.log.error(f"Out-of-order response: expected ID {self.exp_output[0].id}, "
                                     f"got ID {actual.id}")
                    self.scoreboard.errors += 1
                    assert False
                expected = self.exp_output.pop(0)
            else:
                # Out-of-order mode: search for matching transaction by ID within reorder_depth window
                reorder_depth = self.packets_expected
                found_idx = None
                for i in range(min(reorder_depth, len(self.exp_output))):
                    if self.exp_output[i].id == actual.id:
                        found_idx = i
                        break

                if found_idx is None:
                    cocotb.log.error(f"No matching expected transaction found for packet ID {actual.id} "
                                     f"within reorder_depth={reorder_depth}")
                    self.scoreboard.errors += 1
                    assert False

                expected = self.exp_output.pop(found_idx)

            self.packets_received += 1

            # Free the address range by packet ID when packet is received
            pkt_id = actual.id
            removed = self.addr_tracker.remove_range_by_id(pkt_id)
            if not removed:
                cocotb.log.warning(f"Could not remove address range for packet ID {pkt_id}")
            # Mark ID as available for reuse (whether or not remove succeeded)
            self.ids_in_use.discard(pkt_id)

            match, msg = _compare_transactions(expected, actual, self.packets_received)
            if not match:
                cocotb.log.error(f"Packet mismatch: {msg}")
                self.scoreboard.errors += 1
                assert False
            return match

        self.scoreboard.add_interface(self.user_resp_mon, self.exp_output, compare_fn=compare_wrapper)

        if debug:
            self.user_req_drv.log.setLevel(cocotb.logging.DEBUG)
            self.pcie_up_mon.log.setLevel(cocotb.logging.DEBUG)
            self.pcie_down_drv.log.setLevel(cocotb.logging.DEBUG)
            self.user_resp_mon.log.setLevel(cocotb.logging.DEBUG)

    def model(self, instr: PprInstr, mfb_pkt: bytes):
        """Model of the DUT"""
        req_id, req_addr, length_full = instr.id, instr.address, instr.length

        response = PprData()
        response.data = mfb_pkt
        response.id = req_id

        # Write packet to RAM. The responder (PprRequester) will read it from there and send it to the DUT.
        self.ram.w(req_addr, mfb_pkt)

        # Track this address range as in-use, associated with packet ID
        self.addr_tracker.add_range(req_addr, length_full, pkt_id=req_id)

        # Connect to Scoreboard expected output
        self.exp_output.append(response)

    async def reset(self):
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 10)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)


# NOTE: You can also configure a different PAGE_SIZE parameter -> must be done in the DUT.
@cocotb.test()
async def run_test(dut, frame_count=10000, frame_size_min=60, frame_size_max=1500, pcie_mrrs=512, pcie_mps=256, pcie_rcb=64):
    assert pcie_mrrs in [128, 256, 512, 1024, 2048, 4096], "PCIE_MRRS must be one of the standard values."
    assert pcie_mps in [128, 256, 512, 1024, 2048, 4096], "PCIE_MPS must be one of the standard values."
    assert pcie_rcb in [64, 128], "PCIE_RCB must be one of the standard values."

    dut.RESET.value = 1
    cocotb.start_soon(Clock(dut.CLK, 5, units='ns').start())

    tb = Testbench(dut, debug=False, pkts_exp=frame_count, mps=pcie_mps, rcb=pcie_rcb)
    # Change MVB driver's IdleGenerator to ItemRateLimiter
    idle_gen_conf = dict(random_idles=True, max_idles=3, zero_idles_chance=80)
    tb.user_req_drv.set_idle_generator(ItemRateLimiter(rate_percentage=50, **idle_gen_conf))
    await tb.reset()
    tb.dut.PCIE_MRRS.value = pcie_mrrs

    cocotb.log.info("\n--- Beginning the test ---\n")

    tb.pcie_up_drv.start((i, 3) for i in itertools.count())
    tb.user_resp_drv.start((i, 3) for i in itertools.count())
    await ClockCycles(tb.dut.CLK, 10)

    next_id = 0
    max_id = 2**tb.dut.ID_WIDTH.value
    id_mask = max_id - 1
    for mfb_pkt in random_packets(frame_size_min, frame_size_max, frame_count):
        length = len(mfb_pkt)
        # Find a non-overlapping address using the tracker
        addr = tb.addr_tracker.find_non_overlapping_address(length)
        if addr is None:
            cocotb.log.warning(f"Could not find non-overlapping address for packet of length {length}, waiting...")
            # Wait a bit and try again
            await ClockCycles(dut.CLK, 100)
            addr = tb.addr_tracker.find_non_overlapping_address(length)
            if addr is None:
                raise RuntimeError(f"Could not find available address range for packet of length {length}")

        # Wait for an available ID (one that is not currently in use)
        # This ensures IDs are not reused before previous packets are received
        # Increase ID_WIDTH generic in DUT to be over log2(frame_count) to avoid waiting.
        while len(tb.ids_in_use) >= max_id:
            cocotb.log.debug(f"All IDs in use ({len(tb.ids_in_use)}), waiting...")
            await ClockCycles(dut.CLK, 20)

        # Find next available ID
        while next_id in tb.ids_in_use:
            next_id = (next_id + 1) & id_mask

        # Generate a MVB instruction for each packet
        user_instr = PprInstr()
        user_instr.id = next_id
        user_instr.address = addr
        user_instr.length = length

        # Mark ID as in-use before sending
        tb.ids_in_use.add(next_id)

        # Send to Driver (DUT)
        tb.user_req_drv.append(user_instr)
        # Send to Model
        tb.model(user_instr, mfb_pkt)

        # Move to next ID for the following packet
        next_id = (next_id + 1) & id_mask

    # Wait for at least the first packet to reach the DUT's output
    await ClockCycles(dut.CLK, 1000)
    last_num = 0
    while (this_num := tb.user_resp_mon.frame_cnt) > last_num:
        last_num = this_num
        cocotb.log.info(f"Number of transactions processed: {tb.user_resp_mon.frame_cnt}")
        await ClockCycles(dut.CLK, 5000)

    cocotb.log.info("\n--- Test complete, getting results ---\n")
    raise tb.scoreboard.result
