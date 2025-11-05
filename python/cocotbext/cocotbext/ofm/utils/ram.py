# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>

from .binary import Binary
from .math import ceildiv, bitmask


class RAM:
    def __init__(self, capacity):
        self._mem = bytearray(capacity)

    def wint(self, addr, integer, byte_count, byteorder="little"):
        self.w(addr, integer.to_bytes(byte_count, byteorder=byteorder))

    def rint(self, addr, byte_count, byteorder="little"):
        return int.from_bytes(self.r(addr, byte_count), byteorder=byteorder)

    def w(self, addr, byte):
        self._mem[addr: addr + len(byte)] = byte

    def r(self, addr, byte_count):
        return self._mem[addr: addr + byte_count]


class VWWRAM:
    """
    RAM with variable word width.

    Args:
        capacity: number of word stored.
        word_width: width of one word in bits.
    """
    def __init__(self, capacity: int, word_width: int = 8, block_width: int | None = None):
        self._mem = [0] * capacity
        self._capacity = capacity
        self._word_width = word_width
        self._block_width = block_width

    def _len_(self):
        return self._capacity

    def clear_memory(self):
        self._mem = [0] * self._capacity

    def write_word(self, address: int, data: int) -> None:
        self._mem[address] = data

    def read_word(self, address: int) -> int:
        return self._mem[address]

    def write(self, address: int, data: bytes) -> None:
        width = self._word_width
        data_bin = Binary(data)
        word_cnt = ceildiv(width, len(data) * 8) if self._block_width is None else (len(data) * 8) // width

        for i in range(word_cnt):
            self._mem[address + i] = data_bin[i * width : (i + 1) * width].int

        if self._block_width is not None:
            if (remainder_width := (len(data) * 8) % width) > 0:
                blocks = ceildiv(self._block_width, remainder_width)
                self._mem[address + word_cnt] = self._mem[address + word_cnt] & (~bitmask(blocks * self._block_width))
                self._mem[address + word_cnt] += data_bin[word_cnt * width : (word_cnt + 1) * width].int

    def read(self, address: int, byte_count: int) -> bytes:
        width = self._word_width
        word_cnt = ceildiv(width, byte_count * 8)
        data_bin = Binary(bits=byte_count)

        for i in range(word_cnt):
            data_bin[i * width : (i + 1) * width] = self._mem[address + i]

        return data_bin.bytes
