# cocotb_test.py:
# Copyright (C) 2025-2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import itertools
from random import randint
from math import log2, ceil
from typing import Tuple

import cocotb
import logging
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb_bus.drivers import BitDriver
from cocotb_bus.scoreboard import Scoreboard

from cocotbext.ofm.mfb.drivers import MFBDriver
from cocotbext.ofm.mfb.monitors import MFBMonitor
from cocotbext.ofm.mvb.monitors import MVBMonitor
from cocotbext.ofm.mvb.transaction import MvbTrClassic
from cocotbext.ofm.base.generators import ItemRateLimiter
from cocotbext.ofm.ver.generators import random_packets
from cocotbext.ofm.utils.header import SerializableHeader
from cocotbext.ofm.axi4stream.drivers import Axi4StreamMaster
from cocotbext.ofm.axi4stream.transaction import Axi4StreamTransaction

from transaction import MvbTrAddressAndLength
from drivers import MvbDriverAddressAndLength as MVBDriver


# A copy from the dma_bus_pack.vhd
class DmaUphdr(SerializableHeader):
    items = [
        ('dma_request_length', 11),
        ('dma_request_type', 1),
        ('dma_request_firstib', 2),
        ('dma_request_lastib', 2),
        ('dma_request_tag', 8),
        ('dma_request_unitid', 8),
        ('dma_request_global', 64),
        ('dma_request_vfid', 8),
        ('dma_request_pasid', 0),
        ('dma_request_pasidvld', 0),
        ('dma_request_relaxed', 1),
    ]


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
        self.mvb_tx_mon = MVBMonitor(dut, "TX_MVB", dut.CLK)

        self.model_sent = 0
        self.mvb_expected_output = []
        self.mfb_expected_output = []
        self.scoreboard = Scoreboard(dut)
        self.scoreboard.add_interface(self.mvb_tx_mon, self.mvb_expected_output)
        self.scoreboard.add_interface(self.mfb_tx_mon, self.mfb_expected_output)

        if debug:
            if self.mfb_rx_drv is not None:
                self.mfb_rx_drv.log.setLevel(logging.DEBUG)
            if self.axis_rx_drv is not None:
                self.axis_rx_drv.log.setLevel(logging.DEBUG)
            self.mvb_rx_drv.log.setLevel(logging.DEBUG)
            self.mfb_tx_mon.log.setLevel(logging.DEBUG)
            self.mvb_tx_mon.log.setLevel(logging.DEBUG)

    def model(self, instr: MvbTrAddressAndLength, meta: Tuple[int, int], packet: bytes):
        """Model of the DUT"""
        addr, length = instr.address, instr.length
        pcie_mps, page_size = meta

        # PAGE break
        pb_parts = []
        log2_page_size = ceil(log2(page_size))
        page_addr = addr >> log2_page_size
        # Packet goes over at least one page (comparing the top bits indicating the number of the page)
        if ((addr + length) >> log2_page_size) != (page_addr):
            len_reminder = page_size - (addr & 2**log2_page_size-1)
            length -= len_reminder
            pb_parts.append((addr, len_reminder))
            while length > page_size:
                page_addr += 1
                pb_parts.append((page_addr << log2_page_size, page_size))
                length -= page_size
            if length > 0:
                page_addr += 1
                pb_parts.append((page_addr << log2_page_size, length))
        else:
            pb_parts.append((addr, length))

        # MPS break
        all_parts = []
        for p in pb_parts:
            addr, length = p
            while length > pcie_mps:
                all_parts.append((addr, pcie_mps))
                addr += pcie_mps
                length -= pcie_mps
            all_parts.append((addr, length))

        # Create DMA headers and split packets accordingly to the instructions (all_parts)
        for p in all_parts:
            addr, length = p
            # Create DMA upstream header
            hdr = DmaUphdr()
            # Total bytes is length + byte offset (lower 2 bits of address)
            total_bytes = length + (addr % 4)
            hdr.dma_request_length = (total_bytes + 3) // 4  # Round up to dwords (ceildiv)
            hdr.dma_request_type = 1  # 1=Write
            hdr.dma_request_firstib = addr % 4  # Invalid bytes at start = address offset
            hdr.dma_request_lastib = (-total_bytes) % 4
            hdr.dma_request_tag = self.model_sent
            hdr.dma_request_unitid = 0
            hdr.dma_request_global = addr & ~3  # Dword-aligned address
            hdr.dma_request_vfid = 0
            hdr.dma_request_pasid = 0
            hdr.dma_request_pasidvld = 0
            hdr.dma_request_relaxed = 0
            # Convert to MVB transaction
            mvb_instr_model = MvbTrClassic()
            mvb_instr_model.data = hdr.serialize()
            # Connect to Scoreboard expected output
            self.mvb_expected_output.append(mvb_instr_model)
            self.mfb_expected_output.append(packet[0:length])
            self.model_sent += 1
            # Remove processed part from the packet
            packet = packet[length:]

    async def reset(self):
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 10)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)


# NOTE: Do not set frame_size_max > pcie_mps until the DUT suports multiple breaks per word! TODO: Remove when the DUT is fixed
# NOTE: You can also configure a different PAGE_SIZE parameter -> must be done in the DUT.
@cocotb.test()
async def run_test(dut, frame_count=10000, frame_size_min=60, frame_size_max=256, pcie_mps=256):
    assert frame_size_max <= pcie_mps, "frame_size_max must be less than or equal to PCIE_MPS for this test." # TODO: Remove when the DUT is fixed
    assert pcie_mps in [128, 256, 512, 1024, 2048, 4096, 8192, 16384], "PCIE_MPS must be one of the standard values."

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

    for mfb_pkt in random_packets(frame_size_min, frame_size_max, frame_count):
        addr = randint(0, 2**tb.dut.ADDRESS_WIDTH.value - 1)
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
