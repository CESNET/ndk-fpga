# cocotb_test.py:
# Copyright (C) 2025-2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import itertools
from random import randint
from math import log2, ceil
from typing import Tuple
from dataclasses import fields

import cocotb
import logging
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb_bus.drivers import BitDriver
from cocotb_bus.scoreboard import Scoreboard

from cocotbext.ofm.mfb.drivers import MFBDriver
from cocotbext.ofm.mfb.monitors import MFBMonitor
from cocotbext.ofm.mvb.monitors import MVBMonitor
from cocotbext.ofm.mvb.transaction import MvbTrClassicSerializable, hdrfield, serializableheader
from cocotbext.ofm.base.generators import ItemRateLimiter
from cocotbext.ofm.ver.generators import random_packets
from cocotbext.ofm.axi4stream.drivers import Axi4StreamMaster
from cocotbext.ofm.axi4stream.transaction import Axi4StreamTransaction
from cocotbext.ofm.utils.hex_formatter import format_bytes

from transaction import MvbTrAddressAndLength
from drivers import MvbDriverAddressAndLength as MVBDriver


# A copy from the dma_bus_pack.vhd
@serializableheader()
class DmaUphdr(MvbTrClassicSerializable):
    dma_request_length:  int = hdrfield(11)
    dma_request_type:    int = hdrfield(1)
    dma_request_firstib: int = hdrfield(2)
    dma_request_lastib:  int = hdrfield(2)
    dma_request_tag:     int = hdrfield(8)
    dma_request_unitid:  int = hdrfield(8)
    dma_request_global:  int = hdrfield(64)
    dma_request_vfid:    int = hdrfield(8)
    # pasid/pasidvld: width 0, carry no bits — OMIT
    dma_request_relaxed: int = hdrfield(1)


class DUTPacketSegment:
    """Model of one output packet segment produced by the DUT.

    The DUT extends each broken packet segment from the start by ``firstib``
    invalid bytes (to make the address DWORD-aligned) and from the end by
    ``lastib`` invalid bytes (to round the total length up to whole DWORDs).
    The invalid bytes contain random data and cannot be reproduced by the model.
    Therefore the comparator ignores the value of the padding bytes and checks
    only the ``length`` original packet bytes, which start at byte offset
    ``firstib`` inside the extended segment.
    """
    __slots__ = ("addr", "length", "firstib", "lastib", "global_addr",
                 "tag", "orig_packet", "full_packet")

    def __init__(self, addr: int, length: int, tag: int, orig_packet: bytes,
                 firstib: int, lastib: int, full_packet: bytes = b""):
        self.addr = addr
        self.length = length
        self.firstib = firstib
        self.lastib = lastib
        self.global_addr = addr & ~3
        self.tag = tag
        self.orig_packet = orig_packet
        self.full_packet = full_packet

    @property
    def total_bytes(self) -> int:
        return self.length + self.firstib + self.lastib

    @property
    def dwords(self) -> int:
        return (self.total_bytes + 3) // 4

    @property
    def extended_len(self) -> int:
        return self.dwords * 4


def _page_break(addr: int, length: int, page_size: int):
    """Split a byte range by page boundaries.

    Returns a list of (address, length) tuples.  ``length`` is the number of
    *original* bytes in each page chunk; the sum of lengths equals the input
    ``length``.
    """
    log2_page = ceil(log2(page_size))
    page_mask = page_size - 1

    start_page = addr >> log2_page
    end_addr = addr + length
    end_page = end_addr >> log2_page

    parts = []
    rem = length
    cur_addr = addr
    if end_page != start_page:
        first_len = page_size - (addr & page_mask)
        parts.append((cur_addr, first_len))
        rem -= first_len
        cur_addr = (start_page + 1) << log2_page
        while rem > page_size:
            parts.append((cur_addr, page_size))
            rem -= page_size
            cur_addr += page_size
    if rem > 0:
        parts.append((cur_addr, rem))
    return parts


def _mps_break(addr: int, length: int, mps: int):
    """Split a byte range by PCIe MPS.

    The first chunk may contain fewer *original* bytes because the address is
    not DWORD-aligned and the leading invalid bytes count against the MPS
    budget.  The TLP itself still carries up to ``mps`` payload bytes.  After
    the first chunk the address becomes DWORD-aligned, so subsequent chunks use
    the full MPS for original data.
    """
    parts = []
    offset = addr % 4
    rem = length
    cur_addr = addr
    while rem + offset > mps:
        chunk = mps - offset
        parts.append((cur_addr, chunk))
        cur_addr += chunk
        rem -= chunk
        offset = 0
    if rem > 0 or (length == 0):
        parts.append((cur_addr, rem))
    return parts


class testbench():
    def __init__(self, dut, debug=False):
        self.dut = dut
        if dut.AXI_RX_DIRECT.value:
            self.axis_rx_drv = Axi4StreamMaster(dut, "RX_AXI", dut.CLK)
            self.mfb_rx_drv = None
        else:
            self.mfb_rx_drv = MFBDriver(dut, "RX_MFB", dut.CLK)
            self.axis_rx_drv = None
        self.mvb_rx_drv = MVBDriver(dut, "RX_MVB", dut.CLK)
        self.mfb_tx_drv = BitDriver(dut.TX_MFB_DST_RDY, dut.CLK)
        self.mvb_tx_drv = BitDriver(dut.TX_MVB_DST_RDY, dut.CLK)
        self.mfb_tx_mon = MFBMonitor(dut, "TX_MFB", dut.CLK)
        self.mvb_tx_mon = MVBMonitor(dut, "TX_MVB", dut.CLK, tr_type=DmaUphdr)

        self.mvb_expected_output = []
        self.mfb_expected_output = []
        self.scoreboard = Scoreboard(dut)
        self.scoreboard.add_interface(self.mvb_tx_mon, self.mvb_expected_output)
        self.scoreboard.add_interface(self.mfb_tx_mon, self.mfb_expected_output,
                                      compare_fn=self._compare_mfb_segment)

        self.model_sent = 0
        self.tag_bitwidth = next(f.metadata['width'] for f in fields(DmaUphdr) if f.name == 'dma_request_tag')

        if debug:
            if self.mfb_rx_drv is not None:
                self.mfb_rx_drv.log.setLevel(logging.DEBUG)
            if self.axis_rx_drv is not None:
                self.axis_rx_drv.log.setLevel(logging.DEBUG)
            self.mvb_rx_drv.log.setLevel(logging.DEBUG)
            self.mfb_tx_mon.log.setLevel(logging.DEBUG)
            self.mvb_tx_mon.log.setLevel(logging.DEBUG)

    def _compare_mfb_segment(self, actual: bytes):
        """Scoreboard compare function for MFB output segments.

        Only the original packet bytes inside the extended segment are compared;
        the leading and trailing invalid bytes contain DUT-specific random data
        and are intentionally ignored.
        """
        if not self.mfb_expected_output:
            cocotb.log.error("Received unexpected MFB segment")
            return

        exp: DUTPacketSegment = self.mfb_expected_output.pop(0)
        start = exp.firstib
        end = start + exp.length

        match = (
            len(actual) == exp.extended_len
            and actual[start:end] == exp.orig_packet
        )

        if match:
            return

        exp_full_segment = bytes(exp.firstib) + exp.orig_packet + bytes(exp.lastib)

        lines = []
        lines.append("")
        lines.append("#" + "=" * 64 + "#")
        lines.append("#" + " " * 18 + f"MFB SEGMENT MISMATCH (tag {exp.tag})" + " " * 19 + "#")
        lines.append("#" + "=" * 64 + "#")
        lines.append(f"#  Expected (model): address=0x{exp.addr:08x}, global=0x{exp.global_addr:08x}")
        lines.append(f"#  Expected (model): firstib={exp.firstib}, lastib={exp.lastib}")
        lines.append("#" + "=" * 64 + "#")
        lines.append("")

        lines.append(format_bytes(exp_full_segment, label=f"Expected full segment ({len(exp_full_segment)} bytes)"))
        lines.append("")
        lines.append(format_bytes(exp.full_packet, label=f"Expected original packet bytes ({len(exp.full_packet)} bytes)"))
        lines.append("")
        lines.append(format_bytes(actual, label=f"Actual DUT segment ({len(actual)} bytes)"))

        if len(actual) >= end:
            bad = [i for i in range(start, end) if actual[i] != exp.orig_packet[i - start]]
            if bad:
                lines.append("")
                diff_msg = f"Byte differences (segment offsets): {bad[:16]}"
                if len(bad) > 16:
                    diff_msg += f"... ({len(bad)} total)"
                lines.append(diff_msg)
                for i in bad[:5]:
                    lines.append(
                        f"  offset {i}: expected 0x{exp.orig_packet[i - start]:02x}, "
                        f"got 0x{actual[i]:02x}"
                    )
                if len(bad) > 5:
                    lines.append(f"  ... and {len(bad) - 5} more differing bytes")
        else:
            lines.append("")
            lines.append(
                f"Actual segment is shorter than expected; cannot compare bytes "
                f"(need at least {end} bytes, got {len(actual)})."
            )

        self.scoreboard.errors += 1
        raise AssertionError("\n".join(lines))

    def model(self, instr: MvbTrAddressAndLength, meta: Tuple[int, int], packet: bytes):
        """Model of the DUT.

        The model mirrors the hardware pipeline:

        1. The original packet length is split by page boundaries, then by PCIe
           MPS.  The first chunk of each split is shortened by the address's
           DWORD offset because the leading invalid bytes count against the
           page/MPS budget.
        2. For each resulting sub-instruction ``(addr_i, len_i)`` the DUT
           rounds the transfer up to whole DWORDs by adding ``firstib`` leading
           invalid bytes (the address offset) and ``lastib`` trailing invalid
           bytes.
        3. The packet breaker cuts ``len_i`` original bytes from the packet and
           the packet extender produces a segment of ``ceil((len_i + firstib +
           lastib) / 4) * 4`` bytes.
        """
        addr, length = instr.address, instr.length
        pcie_mps, page_size = meta

        # 1) Split the original packet length by page and MPS.
        page_parts = _page_break(addr, length, page_size)
        all_parts = []
        for paddr, plen in page_parts:
            all_parts.extend(_mps_break(paddr, plen, pcie_mps))

        # 2) For each sub-instruction compute the segment parameters.
        for paddr, plen in all_parts:
            firstib = paddr % 4
            total_with_firstib = plen + firstib
            lastib = (-total_with_firstib) % 4

            full_packet = packet
            seg_orig = packet[:plen]
            packet = packet[plen:]

            seg = DUTPacketSegment(
                addr=paddr,
                length=plen,
                tag=self.model_sent & (2**self.tag_bitwidth - 1),
                orig_packet=seg_orig,
                firstib=firstib,
                lastib=lastib,
                full_packet=full_packet,
            )

            # 3) Build the expected DMA upstream header.
            hdr = DmaUphdr(
                dma_request_length=seg.dwords,
                dma_request_type=1, # 1=Write
                dma_request_firstib=seg.firstib,
                dma_request_lastib=seg.lastib,
                dma_request_tag=seg.tag,
                dma_request_unitid=0,
                dma_request_global=seg.global_addr,
                dma_request_vfid=0,
                dma_request_relaxed=0)

            self.mvb_expected_output.append(hdr)
            self.mfb_expected_output.append(seg)
            self.model_sent += 1

    async def reset(self):
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 10)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)


async def _run_test(
    dut,
    frame_count: int = 10000,
    frame_size_min: int = 60,
    frame_size_max: int = 256,
    pcie_mps: int = 256,
    addr_gen=lambda: randint(0, 2**64 - 1)
):
    assert pcie_mps in [128, 256, 512, 1024, 2048, 4096], "PCIE_MPS must be one of the standard values."

    dut.RESET.value = 1
    cocotb.start_soon(Clock(dut.CLK, 5, unit='ns').start())

    tb = testbench(dut)
    # Change MVB driver's IdleGenerator to ItemRateLimiter
    idle_gen_conf = dict(random_idles=True, max_idles=3, zero_idles_chance=80)
    tb.mvb_rx_drv.set_idle_generator(ItemRateLimiter(rate_percentage=50, **idle_gen_conf))
    # TODO: Change MFB driver's IdleGenerator to EthernetRateLimiter
    # MFB Drive first needs to implement support for IdleGenerator!
    await tb.reset()
    tb.dut.PCIE_MPS.value = pcie_mps

    cocotb.log.info("\n--- Beginning the test ---\n")

    tb.mvb_tx_drv.start((i, 3) for i in itertools.count())
    tb.mfb_tx_drv.start((i, 3) for i in itertools.count())
    await ClockCycles(tb.dut.CLK, 10)

    # Decrease max size of generated frames in case the DUT generics do not allow it
    pkt_mtu = tb.dut.PKT_MTU.value
    if frame_size_max > pkt_mtu:
        frame_size_max = pkt_mtu

    for mfb_pkt in random_packets(frame_size_min, frame_size_max, frame_count):
        addr = addr_gen()
        length = len(mfb_pkt)
        # Generate a MVB instruction for each packet
        mvb_instr = MvbTrAddressAndLength()
        mvb_instr.address = addr
        mvb_instr.length = length

        # Send to Driver (DUT)
        if tb.mfb_rx_drv is not None:
            tb.mfb_rx_drv.append(mfb_pkt)
        else:
            axis_tr = Axi4StreamTransaction()
            axis_tr.TDATA = mfb_pkt
            tb.axis_rx_drv.append(axis_tr)
        tb.mvb_rx_drv.append(mvb_instr)

        # Send to Model
        tb.model(instr=mvb_instr, meta=(pcie_mps, tb.dut.PAGE_SIZE.value), packet=mfb_pkt)

    await ClockCycles(dut.CLK, 1000) # Wait for at least the first packet to reach the DUT's output
    last_num = 0
    while (this_num := tb.mfb_tx_mon.frame_cnt) > last_num:
        last_num = this_num
        cocotb.log.info(f"Number of transactions processed: {tb.mfb_tx_mon.frame_cnt}")
        await ClockCycles(dut.CLK, 5000)

    cocotb.log.info("\n--- Test complete, getting results ---\n")
    raise tb.scoreboard.result


# NOTE: Do not set frame_size_max > pcie_mps until the DUT suports multiple breaks per word! TODO: Remove when the DUT is fixed
# NOTE: You can also configure a different PAGE_SIZE parameter -> must be done in the DUT.
@cocotb.test()
async def run_test(dut, frame_count=10000, frame_size_min=60, frame_size_max=256, pcie_mps=256):
    assert frame_size_max <= pcie_mps, "frame_size_max must be less than or equal to PCIE_MPS for this test." # TODO: Remove when the DUT is fixed

    await _run_test(
        dut,
        frame_count=frame_count,
        frame_size_min=frame_size_min,
        frame_size_max=frame_size_max,
        pcie_mps=pcie_mps,
        addr_gen=lambda: randint(0, 2**dut.ADDRESS_WIDTH.value - 1)
    )


# NOTE: Another test variant that would avoid the unspported multiple breaks per word in the DUT.
#       In this test, we make sure the generated addresses are page-aligned so no page-break occurs.
#       This way, we can have packet sizes of arbitrary length.
@cocotb.test()
async def run_test_page_aligned_frames(dut, frame_count=2000, frame_size_min=60, frame_size_max=8192, pcie_mps=256):

    page_size = dut.PAGE_SIZE.value
    address_width = dut.ADDRESS_WIDTH.value
    assert page_size & (page_size - 1) == 0, "PAGE_SIZE must be a power of two for the page-aligned workaround."

    def _page_aligned_addr():
        # Page-aligning the address
        return randint(0, (2**address_width) // page_size) * page_size

    await _run_test(
        dut,
        frame_count=frame_count,
        frame_size_min=frame_size_min,
        frame_size_max=frame_size_max,
        pcie_mps=pcie_mps,
        addr_gen=_page_aligned_addr
    )
