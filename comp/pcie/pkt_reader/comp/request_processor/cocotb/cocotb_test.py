# cocotb_test.py:
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import itertools
from random import randint
from math import log2, ceil
from collections import deque
from dataclasses import fields

import cocotb
import logging
from cocotb.clock import Clock
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb_bus.drivers import BitDriver
from cocotb_bus.scoreboard import Scoreboard

from cocotbext.ofm.mvb.monitors import MVBMonitor
from cocotbext.ofm.base.generators import ItemRateLimiter
from cocotbext.ofm.ver.generators import random_packets

from transaction import PprInstr, IdMemTr, TagMemTr
from drivers import PprDriver
from monitors import IdMemMonitor, TagMemMonitor
from probe import DmaUphdr, PprProbeInterface, PprProbe


class testbench():
    def __init__(self, dut, debug=False):
        self.dut = dut
        self.rx_mvb_drv = PprDriver(dut, "RX_MVB", dut.CLK)
        self.tx_mvb_drv = BitDriver(dut.TX_MVB_DST_RDY, dut.CLK)
        self.tx_mvb_mon = MVBMonitor(dut, "TX_MVB", dut.CLK, tr_type=DmaUphdr)
        self.idmem_mon = IdMemMonitor(dut, "IDMEM", dut.CLK)
        self.tagmem_mon = TagMemMonitor(dut, "TAGMEM", dut.CLK)

        self.tx_mvb_exp_output = []
        self.idmem_exp_output = []
        self.tagmem_exp_output = []
        self.model_sent = 0
        # For the ID Memory - address to READ the completed packets from the Main Memory.
        # Identifies the `word` in the Main Memory where the packet starts.
        # Needs to be initialized only once.
        self._mem_base_addr = 0
        # Create a queue for Tags and initialize it with all possible Tags specified by the bitwidth in the DmaUphdr.
        self.tag_bitwidth = next(f.metadata['width'] for f in fields(DmaUphdr) if f.name == 'dma_request_tag')
        self.tag_q = deque(range(2**self.tag_bitwidth))
        # Queue of used tags to be recycled, filled by the PprProbe
        self.used_tags_q = deque()
        # Setting up the probe to monitor received tags, then put them into the used_tags_q to recycle them.
        self.tx_mvb_probe = PprProbe(self.used_tags_q, PprProbeInterface(self.tx_mvb_mon))

        self.scoreboard = Scoreboard(dut)
        self.scoreboard.add_interface(self.tx_mvb_mon, self.tx_mvb_exp_output)
        self.scoreboard.add_interface(self.idmem_mon, self.idmem_exp_output)
        self.scoreboard.add_interface(self.tagmem_mon, self.tagmem_exp_output)

        if debug:
            self.rx_mvb_drv.log.setLevel(logging.DEBUG)
            self.tx_mvb_mon.log.setLevel(logging.DEBUG)
            self.idmem_mon.log.setLevel(logging.DEBUG)
            self.tagmem_mon.log.setLevel(logging.DEBUG)

    async def model(self, instr: PprInstr):
        """Model of the DUT"""
        req_id, req_addr, length_full = instr.id, instr.address, instr.length
        pcie_mrrs = self.dut.PCIE_MRRS.value.to_unsigned()
        page_size = self.dut.PAGE_SIZE.value
        memory_size = self.dut.MEMORY_ITEMS.value
        bytes_per_word = self.dut.MEMORY_ITEM_WIDTH.value // 8

        # For the Tag Memory - address to WRITE read responses to the Main Memory.
        # Identifies the `byte` within the Main Memory word where a partial (read response) transaction will be stored.
        # The `word` is identified by self._mem_base_addr.
        mem_word_addr = 0

        # PAGE break
        req_len = length_full
        pb_parts = []
        log2_page_size = ceil(log2(page_size))
        page_addr = req_addr >> log2_page_size
        # Packet goes over at least one page (comparing the top bits indicating the number of the page)
        if ((req_addr + req_len) >> log2_page_size) != (page_addr):
            len_reminder = page_size - (req_addr & (2**log2_page_size - 1))
            req_len -= len_reminder
            pb_parts.append((req_addr, len_reminder))
            while req_len > page_size:
                page_addr += 1
                pb_parts.append((page_addr << log2_page_size, page_size))
                req_len -= page_size
            if req_len > 0:
                page_addr += 1
                pb_parts.append((page_addr << log2_page_size, req_len))
        else:
            pb_parts.append((req_addr, req_len))

        # MRRS break
        all_parts = []
        for p in pb_parts:
            req_addr, req_len = p
            addr_offset = req_addr % 4
            # Unaligned start reduces usable space in the first chunk
            while req_len + addr_offset > pcie_mrrs:
                chunk_len = pcie_mrrs - addr_offset
                all_parts.append((req_addr, chunk_len))
                req_addr += chunk_len
                req_len -= chunk_len
                addr_offset = 0  # subsequent chunks are dword-aligned
            all_parts.append((req_addr, req_len))

        # Need a clone of the base addres for TagMem transactions; necessary when addressing transactions wrapping around the Main Memory's end.
        new_mem_base_addr = self._mem_base_addr
        # Create DMA headers and split packets accordingly to the instructions (all_parts)
        for p in all_parts:
            req_addr, req_len = p
            addr_offset = req_addr % 4
            # Total bytes is length + byte offset (lower 2 bits of address)
            total_bytes = req_len + addr_offset

            # Create DMA upstream header transaction
            hdr = DmaUphdr(
                dma_request_length=(total_bytes + 3) // 4, # Round up to dwords (ceildiv)
                dma_request_type=0, # 0=Read
                dma_request_firstib=addr_offset, # Invalid bytes at start = address offset
                dma_request_lastib=(-total_bytes) % 4,
                dma_request_tag=self.model_sent & (2**self.tag_bitwidth - 1),
                dma_request_unitid=0,
                dma_request_global=req_addr & ~3, # Dword-aligned address
                dma_request_vfid=0,
                dma_request_relaxed=0)
            # Connect to Scoreboard expected output
            self.tx_mvb_exp_output.append(hdr)
            self.model_sent += 1

            # Create TagMem transaction
            tagmem_tr = TagMemTr()
            while len(self.tag_q) == 0:
                # The reason the Model must be async - sleep freezes the simulation
                await RisingEdge(self.dut.CLK)
            tagmem_tr.tag = self.tag_q.popleft()
            # addr_extended: top bits address the word in the Main Memory, bottom bits address the byte within the word
            addr_extended = (new_mem_base_addr << ceil(log2(bytes_per_word))) + mem_word_addr
            # Wrap around after reaching max address (= memory size) and update addresses for the next part
            if addr_extended >= (memory_size << ceil(log2(bytes_per_word))):
                addr_extended &= (memory_size << ceil(log2(bytes_per_word))) - 1
                new_mem_base_addr = addr_extended >> ceil(log2(bytes_per_word))
                mem_word_addr = addr_extended & (bytes_per_word - 1)
            tagmem_tr.addr = addr_extended
            tagmem_tr.id = req_id
            tagmem_tr.firstib = addr_offset  # Invalid bytes at start = address offset
            # Connect to Scoreboard expected output
            self.tagmem_exp_output.append(tagmem_tr)
            # Update the word address (can accumulate over multiple words)
            mem_word_addr += req_len

        # Create IdMem transaction
        words_roundedup = ceil(length_full / (bytes_per_word))
        idmem_tr = IdMemTr()
        idmem_tr.id = req_id
        idmem_tr.addr = self._mem_base_addr
        idmem_tr.words = words_roundedup
        idmem_tr.eof_pos = (length_full - 1) & (bytes_per_word - 1) # Mask top bits of length
        idmem_tr.tag_cnt = len(all_parts)
        # Connect to Scoreboard expected output
        self.idmem_exp_output.append(idmem_tr)
        # Update the base address, then mask it to keep only the address bits + 1 extra bit (as required by the DUT)
        self._mem_base_addr += words_roundedup
        self._mem_base_addr %= (memory_size << 1)

    async def reset(self):
        self.dut.RESET.value = 1
        await ClockCycles(self.dut.CLK, 10)
        self.dut.RESET.value = 0
        await RisingEdge(self.dut.CLK)

    async def recycle_tags(self):
        """Pops used Tags from the Probe and sends them to the DUT and local Tag queue."""

        while True:
            if self.dut.dma_uphdr_gen_i.init_tags.value == 0 and len(self.used_tags_q) > 0:
                recycled_tag = self.used_tags_q.popleft()
                self.tag_q.append(recycled_tag)
                self.dut.TAGMEM_FREE_TAG.value = recycled_tag
                self.dut.TAGMEM_FREE_VLD.value = 1
            else:
                self.dut.TAGMEM_FREE_TAG.value = 0
                self.dut.TAGMEM_FREE_VLD.value = 0
            await RisingEdge(self.dut.CLK)


# NOTE: You can also configure a different PAGE_SIZE parameter -> must be done in the DUT.
@cocotb.test()
async def run_test(dut, frame_count=10000, frame_size_min=60, frame_size_max=1500, pcie_mrrs=256):
    assert pcie_mrrs in [128, 256, 512, 1024, 2048, 4096, 8192, 16384], "PCIE_MRRS must be one of the standard values."

    dut.RESET.value = 1
    cocotb.start_soon(Clock(dut.CLK, 5, unit='ns').start())

    tb = testbench(dut, debug=False)
    # Change MVB driver's IdleGenerator to ItemRateLimiter
    idle_gen_conf = dict(random_idles=True, max_idles=3, zero_idles_chance=80)
    tb.rx_mvb_drv.set_idle_generator(ItemRateLimiter(rate_percentage=50, **idle_gen_conf))
    await tb.reset()
    tb.dut.PCIE_MRRS.value = pcie_mrrs
    cocotb.start_soon(tb.recycle_tags())

    cocotb.log.info("\n--- Beginning the test ---\n")

    tb.tx_mvb_drv.start((i, 3) for i in itertools.count())
    await ClockCycles(tb.dut.CLK, 10)

    id = 0
    id_width = tb.dut.ID_WIDTH.value
    # Get address width from DmaUphdr class (dma_request_global field)
    addr_width = next(f.metadata['width'] for f in fields(DmaUphdr) if f.name == 'dma_request_global')
    # No need to generate packets, but it will be simpler to reuse it in the test for the whole PPR component
    for mfb_pkt in random_packets(frame_size_min, frame_size_max, frame_count):
        addr = randint(0, 2**addr_width - 1)
        length = len(mfb_pkt)
        # Generate a MVB instruction for each packet
        mvb_instr = PprInstr()
        mvb_instr.id = id
        mvb_instr.address = addr
        mvb_instr.length = length

        # Send to Driver (DUT)
        tb.rx_mvb_drv.append(mvb_instr)
        # Send to Model (await model so it can pause without blocking simulator)
        await tb.model(mvb_instr)
        # Next ID - could use random but would neeed to keep track of used IDs (worth the extra work?)
        id += 1
        # Reuse IDs when exceeding the max value - not keeping track of used IDs for simplicity
        id &= (2**id_width - 1)

    # Wait for at least the first packet to reach the DUT's output
    await ClockCycles(dut.CLK, 1000)
    last_num = 0
    while (this_num := tb.tx_mvb_mon.item_cnt) > last_num:
        last_num = this_num
        cocotb.log.info(f"Number of transactions processed: {tb.tx_mvb_mon.item_cnt}")
        await ClockCycles(dut.CLK, 5000)

    cocotb.log.info("\n--- Test complete, getting results ---\n")
    raise tb.scoreboard.result
