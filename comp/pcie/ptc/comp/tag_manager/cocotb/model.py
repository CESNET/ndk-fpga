# model.py: Reference model of the PTC_TAG_MANAGER tag pool and credit budget
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

from dataclasses import dataclass


@dataclass
class InFlightRead:
    """DMA identity and word accounting of one PCIe tag held by an outstanding read."""
    dma_tag: int
    dma_unitid: int
    # DWORD address and length of the original request, plus the part of it that
    # completion chunks already cover. The next chunk continues where they ended.
    addr_dwords: int = 0
    len_dwords: int = 0
    consumed_dwords: int = 0


class TagManagerModel:
    """
    Reference model of the free and the allocated PCIe tags.

    The DUT may assign any free tag in any order. This model therefore checks rules
    that have to hold, instead of predicting the tag of each request. It reports a
    tag allocated twice and a tag out of range. It also reports a wrong DMA Tag or
    ID on the DOWN side and a word budget that is overrun.

    The model numbers the tags the same way as the MVB_UP_TAG_OUT and TAG ports.
    For PCIE_TAG_WIDTH=10 the DUT adds 256 to every tag, so the pool is [256, 767].
    For PCIE_TAG_WIDTH=8 there is no offset and the pool is [0, 255].
    """

    def __init__(self, pcie_tag_width: int, word_size: int = 0,
                 check_cpl_credits: bool = False, available_words: int = 0):
        # Only the two widths used on real hardware are supported. The pool sizes
        # below hold for these two widths alone.
        assert pcie_tag_width in (8, 10), "TagManagerModel only supports PCIE_TAG_WIDTH 8 or 10"
        self.pcie_tag_width = pcie_tag_width
        self.is_10bit = (pcie_tag_width == 10)
        self._offset = 256 if self.is_10bit else 0
        self.pool_size = 512 if self.is_10bit else 256
        # Write requests always carry this placeholder tag. It is the internal tag 0
        # in the external numbering.
        self.write_dummy_tag = self._offset

        self.free: set[int] = set(range(self._offset, self._offset + self.pool_size))
        self.in_flight: dict[int, InFlightRead] = {}

        # Word budget of the Storage FIFOX, the model of free_cplh_reg. One word is
        # MFB_DOWN_REGIONS*MFB_DOWN_REG_SIZE DWORDs. s1_reg_pr and
        # freed_words_adder_input_pr count in these words.
        self.word_size = word_size
        self.check_cpl_credits = check_cpl_credits
        self.available_words = available_words
        self.outstanding_words = 0
        # The largest value of outstanding_words so far. A test uses it to check that
        # the budget was really reached.
        self.max_outstanding_words = 0

    @property
    def capacity(self) -> int:
        """Number of tags in the pool, the free and the allocated ones together."""
        return len(self.free) + len(self.in_flight)

    def alloc_read(self, tag: int, dma_tag: int, dma_unitid: int,
                   addr_dwords: int = 0, len_dwords: int = 0) -> None:
        assert tag in self.free, (
            f"read got tag {tag}, which was not free (double allocation or out of range)")
        self.free.remove(tag)
        self.in_flight[tag] = InFlightRead(dma_tag, dma_unitid, addr_dwords, len_dwords)

        if self.word_size:
            reserved = self._words_for_span(addr_dwords, len_dwords, round_up=True)
            self.outstanding_words += reserved
            self.max_outstanding_words = max(self.max_outstanding_words, self.outstanding_words)
            if self.check_cpl_credits:
                assert self.outstanding_words <= self.available_words, (
                    f"CplD word budget overrun: admitting read on tag {tag} (reserving "
                    f"{reserved} words) raises the reservation to {self.outstanding_words}, "
                    f"over the {self.available_words}-word budget")

    def check_write_tag(self, tag: int) -> None:
        assert tag == self.write_dummy_tag, (
            f"write request got real tag {tag}, expected placeholder {self.write_dummy_tag}")

    def peek_in_flight(self, tag: int) -> InFlightRead:
        assert tag in self.in_flight, f"completion for tag {tag}, which is not allocated"
        return self.in_flight[tag]

    def remaining_len(self, tag: int) -> int:
        """DWORDs of the original request not yet covered by a completion chunk."""
        info = self.peek_in_flight(tag)
        return info.len_dwords - info.consumed_dwords

    def next_chunk_low_addr_bytes(self, tag: int) -> int:
        """Byte address where the next completion chunk of this tag starts, not masked."""
        info = self.peek_in_flight(tag)
        return (info.addr_dwords + info.consumed_dwords) * 4

    def advance_completion(self, tag: int, chunk_len_dwords: int, is_last: bool) -> None:
        """
        Record a completion chunk of chunk_len_dwords for tag. Release the tag when
        is_last is set. This follows freed_words_adder_input_pr: a chunk frees words
        rounded down, because the rest of the request keeps its reservation. The last
        chunk of a tag rounds up instead. The whole sequence of chunks therefore frees
        exactly the reservation that alloc_read made, for any split into chunks.
        """
        info = self.peek_in_flight(tag)
        freed = 0
        if self.word_size:
            freed = self._words_for_span(info.addr_dwords + info.consumed_dwords,
                                         chunk_len_dwords, round_up=is_last)
            self.outstanding_words -= freed
        info.consumed_dwords += chunk_len_dwords
        if is_last:
            self.release(tag)
        if self.word_size and self.check_cpl_credits:
            assert self.outstanding_words >= 0, (
                f"CplD word accounting went negative after freeing tag {tag} "
                f"({freed} words), the model or the testbench miscounts")

    def release(self, tag: int) -> None:
        assert tag in self.in_flight, f"release of tag {tag}, which is not allocated"
        del self.in_flight[tag]
        self.free.add(tag)

    def _words_for_span(self, addr_dwords: int, len_dwords: int, round_up: bool) -> int:
        off = addr_dwords % self.word_size
        words_wide = len_dwords + off
        if round_up:
            return -(-words_wide // self.word_size)  # ceil division
        return words_wide // self.word_size
