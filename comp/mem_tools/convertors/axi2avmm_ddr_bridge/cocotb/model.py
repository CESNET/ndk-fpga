# model.py: Reference model of the memory behind the bridge
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author: David Beneš <benes@dyna-nic.com>, 2026
#
# SPDX-License-Identifier: BSD-3-Clause

"""Reference model of the memory behind the bridge.

The model is word addressed, exactly like the Avalon-MM side of the bridge, and
holds what the Avalon-MM master asked the bridge to store. It is kept
independent of the AXI slave memory so that a read mismatch can be attributed to
the read path even when the write path is broken.
"""


class MemoryModel:
    def __init__(self, word_bytes: int) -> None:
        self.word_bytes = word_bytes
        self._words: dict[int, bytes] = {}

    def byte_address(self, word_address: int) -> int:
        return word_address * self.word_bytes

    def write(self, word_address: int, data: bytes) -> None:
        self._words[word_address] = bytes(data)

    def read(self, word_address: int) -> bytes:
        return self._words.get(word_address, bytes(self.word_bytes))
