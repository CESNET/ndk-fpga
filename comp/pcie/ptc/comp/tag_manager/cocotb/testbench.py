# testbench.py: Testbench infrastructure for PTC_TAG_MANAGER
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import logging
import random
import time

import cocotb
from cocotb.triggers import RisingEdge, ClockCycles
from cocotb_bus.drivers import BitDriver
from cocotbext.ofm.mvb.transaction import MvbTrClassicSerializable, hdrfield, serializableheader
from cocotbext.ofm.ver.backpressure import BackpressureConfig, BackpressureGenerator

from model import TagManagerModel
from scoreboard import Scoreboard

TYPE_READ = 0
TYPE_WRITE = 1

# DMA_REQUEST_LENGTH width, fixed by dma_bus_pack.vhd and not a generic.
DMA_REQUEST_LENGTH_W = 11

# DMA_DOWN_HDR_TAG and DMA_DOWN_HDR_ID become valid this many driver loop iterations
# after TAG is driven. The entity doc says 2 CLK after the TAG input is set, counted
# from the edge on which the DUT samples it. This driver sets TAG just after a rising
# edge, so the DUT samples it one edge later. The values appear at iteration+3.
RECALL_DELAY_ITERATIONS = 3

# A Completion may not arrive before the DUT has stored the mapping of its tag. The
# write into the tag mapping memory comes a few clock cycles after MVB_UP_HDR_OUT, see
# tag_map_wr_reg_pr. On a real link a Completion always comes long after its request.
# The DOWN driver therefore waits this many of its own iterations before it uses a tag.
ADMISSION_DELAY_ITERATIONS = 8


@serializableheader()
class DmaUphdr(MvbTrClassicSerializable):
    """A copy of the DMA UP header layout from dma_bus_pack.vhd."""
    dma_request_length:  int = hdrfield(DMA_REQUEST_LENGTH_W)
    dma_request_type:    int = hdrfield(1)
    dma_request_firstib: int = hdrfield(2)
    dma_request_lastib:  int = hdrfield(2)
    dma_request_tag:     int = hdrfield(8)
    dma_request_unitid:  int = hdrfield(8)
    dma_request_global:  int = hdrfield(64)
    dma_request_vfid:    int = hdrfield(8)
    dma_request_relaxed: int = hdrfield(1)


def unpack_item(word: int, item_width: int, index: int) -> int:
    return (word >> (index * item_width)) & (2**item_width - 1)


class Heartbeat:
    """
    Progress log driven by wall clock time, for long polling loops.

    A log tied to a count, such as "every 1000 reads", stays silent until that count
    is reached. With a small word budget only a few reads run at a time, so that
    silence can last minutes. This class logs after a fixed wall clock time instead,
    whatever the throughput of the DUT.
    """
    def __init__(self, interval_s: float = 10.0):
        self.interval_s = interval_s
        self._last = time.monotonic()

    def tick(self, **fields) -> None:
        now = time.monotonic()
        if now - self._last < self.interval_s:
            return
        self._last = now
        info = ", ".join(f"{k}={v}" for k, v in fields.items())
        cocotb.log.info(f"still running ({info}, sim_time={cocotb.utils.get_sim_time('ns')}ns)")


class Testbench:
    def __init__(self, dut, write_ratio: float = 0.3, debug: bool = False):
        self.dut = dut
        self.log = cocotb.log
        if debug:
            self.log.setLevel(logging.DEBUG)

        self.mvb_up_items = int(dut.MVB_UP_ITEMS.value)
        self.mvb_down_items = int(dut.MVB_DOWN_ITEMS.value)
        self.dma_tag_width = int(dut.DMA_TAG_WIDTH.value)
        self.dma_id_width = int(dut.DMA_ID_WIDTH.value)
        self.pcie_tag_width = int(dut.PCIE_TAG_WIDTH.value)
        self.pcie_low_addr_width = int(dut.PCIE_LOW_ADDR_WIDTH.value)
        self.uphdr_width = len(DmaUphdr())
        self.write_ratio = write_ratio

        word_size = int(dut.MFB_DOWN_REGIONS.value) * int(dut.MFB_DOWN_REG_SIZE.value)
        check_cpl_credits = bool(int(dut.CHECK_CPL_CREDITS.value))
        available_words = int(dut.EXTRA_WORDS.value)
        self.model = TagManagerModel(self.pcie_tag_width, word_size,
                                     check_cpl_credits, available_words)
        self.scoreboard = Scoreboard()

        self.reads_completed = 0
        # Number of completion chunks left for each allocated PCIe tag. It is set when
        # the first chunk of that tag is driven.
        self._chunks_remaining: dict[int, int] = {}
        # Tags whose completions may already be driven
        self._completable: set[int] = set()
        # A new tag waits here for ADMISSION_DELAY_ITERATIONS driver loop iterations
        self._admit_pipe: list[set[int]] = [set() for _ in range(ADMISSION_DELAY_ITERATIONS)]

        dut.RCB_SIZE.value = 0

        self.up_out_backpressure = BitDriver(dut.MVB_UP_HDR_OUT_DST_RDY, dut.CLK)

    async def reset(self) -> None:
        dut = self.dut
        dut.RESET.value = 1
        dut.MVB_UP_HDR_IN_SRC_RDY.value = 0
        dut.MVB_UP_HDR_IN_VLD.value = 0
        dut.MVB_UP_HDR_OUT_DST_RDY.value = 0
        dut.TAG_VLD.value = 0
        dut.TAG_RELEASE.value = 0
        await ClockCycles(dut.CLK, 10)
        dut.RESET.value = 0
        await RisingEdge(dut.CLK)

    def start(self) -> None:
        self.up_out_backpressure.start(BackpressureGenerator(BackpressureConfig(1, 5, 0.5)))
        cocotb.start_soon(self._up_in_driver())
        cocotb.start_soon(self._up_out_monitor())
        cocotb.start_soon(self._down_driver_and_recall_monitor())

    async def _up_in_driver(self) -> None:
        """Generator of random DMA UP requests. It holds the data steady while stalled."""
        dut = self.dut
        pending = False
        while True:
            await RisingEdge(dut.CLK)
            if dut.RESET.value == 1:
                dut.MVB_UP_HDR_IN_SRC_RDY.value = 0
                dut.MVB_UP_HDR_IN_VLD.value = 0
                pending = False
                continue
            if pending and int(dut.MVB_UP_HDR_IN_DST_RDY.value) != 1:
                continue  # still stalled, keep presenting the same word

            pending = False
            if random.random() < 0.2:  # idle cycle
                dut.MVB_UP_HDR_IN_SRC_RDY.value = 0
                dut.MVB_UP_HDR_IN_VLD.value = 0
                continue

            vlds = 0
            hdr_word = 0
            for i in range(self.mvb_up_items):
                if random.random() < 0.75:  # how often a lane carries a request
                    is_write = random.random() < self.write_ratio
                    hdr = DmaUphdr(
                        dma_request_length=random.randint(1, 32),
                        dma_request_type=TYPE_WRITE if is_write else TYPE_READ,
                        dma_request_firstib=0,
                        dma_request_lastib=0,
                        dma_request_tag=random.randint(0, 2**self.dma_tag_width - 1),
                        dma_request_unitid=random.randint(0, 2**self.dma_id_width - 1),
                        dma_request_global=random.randint(0, 2**62 - 1) << 2,
                        dma_request_vfid=0,
                        dma_request_relaxed=0,
                    )
                    hdr_word |= hdr.serialize() << (i * self.uphdr_width)
                    vlds |= (1 << i)

            if vlds == 0:
                dut.MVB_UP_HDR_IN_SRC_RDY.value = 0
                dut.MVB_UP_HDR_IN_VLD.value = 0
                continue

            dut.MVB_UP_HDR_IN_SRC_RDY.value = 1
            dut.MVB_UP_HDR_IN_VLD.value = vlds
            dut.MVB_UP_HDR_IN.value = hdr_word
            pending = True

    async def _up_out_monitor(self) -> None:
        """
        Observes accepted UP output items.

        MVB_UP_HDR_OUT carries the DMA request header unchanged. The original
        dma_request_tag, dma_request_unitid and dma_request_type are read back from it.
        The driver side therefore keeps no list of the requests it has sent.
        """
        dut = self.dut
        while True:
            await RisingEdge(dut.CLK)
            if dut.RESET.value == 1:
                continue
            if int(dut.MVB_UP_HDR_OUT_SRC_RDY.value) != 1 or int(dut.MVB_UP_HDR_OUT_DST_RDY.value) != 1:
                continue
            vld = int(dut.MVB_UP_HDR_OUT_VLD.value)
            if vld == 0:
                continue

            hdr_word = int(dut.MVB_UP_HDR_OUT.value)
            tag_word = int(dut.MVB_UP_TAG_OUT.value)
            for i in range(self.mvb_up_items):
                if not (vld >> i) & 1:
                    continue
                hdr = DmaUphdr.deserialize(unpack_item(hdr_word, self.uphdr_width, i))
                tag = unpack_item(tag_word, self.pcie_tag_width, i)

                if hdr.dma_request_type == TYPE_WRITE:
                    self.scoreboard.check(self.model.check_write_tag, tag)
                else:
                    self.scoreboard.check(
                        self.model.alloc_read, tag, hdr.dma_request_tag, hdr.dma_request_unitid,
                        hdr.dma_request_global >> 2, hdr.dma_request_length)
                    self._admit_pipe[-1].add(tag)

    def _advance_admit_pipe(self) -> None:
        self._completable |= self._admit_pipe.pop(0)
        self._admit_pipe.append(set())

    def _pick_completion_candidates(self) -> list[int]:
        candidates = [t for t in self._completable if random.random() < 0.6]
        random.shuffle(candidates)
        return candidates[: self.mvb_down_items]

    async def _down_driver_and_recall_monitor(self) -> None:
        """
        Drives completions on the DOWN interface. It also checks the DMA Tag and ID
        that the DUT returns on DMA_DOWN_HDR_TAG and DMA_DOWN_HDR_ID.

        Each lane has its own shift register with one slot per driver loop iteration.
        A slot holds the expected pair of dma_request_tag and dma_request_unitid, or
        None. The slot that is due now was filled RECALL_DELAY_ITERATIONS iterations
        ago. The check compares by position, so two chunks of one tag with the same
        values cannot be matched against the wrong iteration.
        """
        dut = self.dut
        pending: list[list] = [[None] * RECALL_DELAY_ITERATIONS for _ in range(self.mvb_down_items)]

        while True:
            await RisingEdge(dut.CLK)

            if dut.RESET.value == 1:
                dut.TAG_VLD.value = 0
                dut.TAG_RELEASE.value = 0
                for lane in range(self.mvb_down_items):
                    pending[lane] = [None] * RECALL_DELAY_ITERATIONS
                continue

            self._advance_admit_pipe()

            # check the entry that is due this iteration, then drop it
            dma_tag_word = int(dut.DMA_DOWN_HDR_TAG.value)
            dma_id_word = int(dut.DMA_DOWN_HDR_ID.value)
            for lane in range(self.mvb_down_items):
                due = pending[lane][0]
                pending[lane] = pending[lane][1:]
                if due is None:
                    continue
                got = (unpack_item(dma_tag_word, self.dma_tag_width, lane),
                       unpack_item(dma_id_word, self.dma_id_width, lane))
                self.scoreboard.check(self._check_recall, lane, due, got)

            # issue new completions
            candidates = self._pick_completion_candidates()
            tag_word = 0
            low_addr_word = 0
            len_word = 0
            release_bits = 0
            vld_bits = 0
            for lane in range(self.mvb_down_items):
                if lane >= len(candidates):
                    pending[lane].append(None)
                    continue
                tag = candidates[lane]
                info = self.model.peek_in_flight(tag)
                chunks_left = self._chunks_remaining.setdefault(tag, random.randint(1, 3))

                # Split the remaining length of the request into this chunk and the
                # chunks still to come, so that the completions cover the request
                # exactly. The word budget accounting is correct only then.
                remaining = self.model.remaining_len(tag)
                if chunks_left <= 1:
                    chunk_len = remaining
                else:
                    max_len = max(1, remaining - (chunks_left - 1))
                    chunk_len = random.randint(1, max_len)
                is_last = chunk_len >= remaining
                low_addr = self.model.next_chunk_low_addr_bytes(tag) % (2**self.pcie_low_addr_width)

                tag_word |= tag << (lane * self.pcie_tag_width)
                len_word |= chunk_len << (lane * DMA_REQUEST_LENGTH_W)
                low_addr_word |= low_addr << (lane * self.pcie_low_addr_width)
                vld_bits |= (1 << lane)
                pending[lane].append((info.dma_tag, info.dma_unitid))

                self.scoreboard.check(self.model.advance_completion, tag, chunk_len, is_last)
                if is_last:
                    release_bits |= (1 << lane)
                    del self._chunks_remaining[tag]
                    self._completable.discard(tag)
                    self.reads_completed += 1
                else:
                    self._chunks_remaining[tag] = chunks_left - 1

            dut.TAG.value = tag_word
            dut.TAG_COMPL_LOW_ADDR.value = low_addr_word
            dut.TAG_COMPL_LEN.value = len_word
            dut.TAG_VLD.value = vld_bits
            dut.TAG_RELEASE.value = release_bits

    @staticmethod
    def _check_recall(lane: int, expected: tuple, got: tuple) -> None:
        assert expected == got, (
            f"lane {lane}: expected DMA tag and id {expected} on DMA_DOWN_HDR_TAG and "
            f"DMA_DOWN_HDR_ID {RECALL_DELAY_ITERATIONS} iterations after the completion, got {got}")
