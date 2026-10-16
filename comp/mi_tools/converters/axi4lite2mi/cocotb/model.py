# model.py: Reference model of the AXI4LITE2MI verification
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2026
#
# SPDX-License-Identifier: BSD-3-Clause

"""Expected MI traffic derived from the AXI4-Lite handshakes.

Every AXI beat maps to exactly one MI request: the address is masked by
ADDR_MASK, a write carries WDATA with WSTRB as byte enables and a read always
enables all bytes. The model works from the observed handshakes, so the order
in which the DUT interleaves reads and writes does not matter; reads and writes
are only compared within their own stream, where the order is fixed.
"""

from dataclasses import dataclass
from typing import Callable

from axil_checker import Handshake
from mi_slave import MiRequest


@dataclass(frozen=True)
class MiAccess:
    write : bool
    addr  : int
    data  : int  # MI_DWR of a write, 0 for a read
    be    : int

    def __str__(self) -> str:
        kind = "WR" if self.write else "RD"
        data = f" data=0x{self.data:08x}" if self.write else ""
        return f"{kind} addr=0x{self.addr:x}{data} be=0x{self.be:x}"


def observed(request: MiRequest) -> MiAccess:
    return MiAccess(request.write, request.addr,
                    int.from_bytes(request.data, "little") if request.write else 0, request.be)


class Model:
    def __init__(self, addr_mask: int, word_bytes: int) -> None:
        self.addr_mask = addr_mask
        self.word_bytes = word_bytes
        self.be_all = 2**word_bytes - 1

    def expected_writes(self, aw: list[Handshake], w: list[Handshake]) -> list[MiAccess]:
        return [MiAccess(True, a.addr & self.addr_mask, d.data, d.strb) for a, d in zip(aw, w)]

    def expected_reads(self, ar: list[Handshake]) -> list[MiAccess]:
        return [MiAccess(False, a.addr & self.addr_mask, 0, self.be_all) for a in ar]

    def expected_memory(self, writes: list[MiAccess], baseline: dict[int, bytes],
                        initial: Callable[[int], bytes]) -> dict[int, bytes]:
        """Memory content after applying the expected writes in order to the baseline."""
        memory = dict(baseline)

        for access in writes:
            word = access.addr // self.word_bytes
            content = bytearray(memory.get(word, initial(word)))
            data = access.data.to_bytes(self.word_bytes, "little")
            for lane in range(self.word_bytes):
                if access.be >> lane & 1:
                    content[lane] = data[lane]
            memory[word] = bytes(content)

        return memory
