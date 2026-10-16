# mi_slave.py: MI slave memory model of the AXI4LITE2MI verification
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2026
#
# SPDX-License-Identifier: BSD-3-Clause

"""MI slave memory terminating the MI master port of the DUT.

The NDK MIResponseDriver replays pre-queued data one cycle after the request is
accepted and does not look at the address, so it can neither act as a memory
nor answer in the same cycle as MI_ARDY or after a random latency. This model
does all three and also checks the MI master side of the DUT.
"""

import random
from collections import deque
from dataclasses import dataclass
from typing import Any, Callable, Iterator, Optional

import cocotb
from cocotb.triggers import ReadWrite, RisingEdge


@dataclass
class MiRequest:
    """One MI request accepted by the slave (MI_ARDY and MI_RD/MI_WR in the same cycle)."""
    write : bool
    addr  : int
    data  : bytes  # MI_DWR for writes, empty for reads
    be    : int
    cycle : int


@dataclass
class _PendingRead:
    due  : int
    data : bytes


def default_content(word_address: int, word_bytes: int) -> bytes:
    """Content of a word that has never been written, unique for every address."""
    return random.Random(word_address).randbytes(word_bytes)


def always(value: bool) -> Iterator[bool]:
    while True:
        yield value


def random_ready(rate: float, rng: random.Random) -> Iterator[bool]:
    """MI_ARDY pattern; rate is the fraction of cycles the slave is not ready."""
    while True:
        yield rng.random() >= rate


class MiSlave:
    """Memory with configurable MI_ARDY backpressure and MI_DRDY latency.

    The read latency is the number of cycles between the cycle in which the
    request is accepted and the cycle with MI_DRDY; 0 answers in the very cycle
    of MI_ARDY. Responses are returned in order, as the MI bus requires.
    """

    def __init__(self, dut: Any, clock: Any, reset: Any, rng: random.Random) -> None:
        self.dut = dut
        self.clock = clock
        self.reset = reset
        self.rng = rng
        self.log = cocotb.log.getChild("mi_slave")

        self.word_bytes = len(dut.MI_DWR) // 8
        self.be_all = 2**self.word_bytes - 1

        self.memory: dict[int, bytes] = {}
        # Memory content at the last clear(); recorded traffic applies on top of it.
        self.baseline: dict[int, bytes] = {}

        self._ready: Iterator[bool] = always(True)
        self._latency: Callable[[], int] = lambda: 0

        self.requests: list[MiRequest] = []
        self.read_data: list[bytes] = []
        self.violations: list[str] = []
        self.checking = False
        self.same_cycle_responses = 0

        self._pending: deque[_PendingRead] = deque()
        self._cycle = 0
        self._drdy_head = False          # MI_DRDY of this cycle comes from the pending queue
        self._same_cycle: Optional[bytes] = None  # data of a 0-latency answer driven this cycle
        self._planned_latency = 0
        self._previous: Optional[tuple] = None  # request held in the previous cycle, not accepted

        dut.MI_ARDY.value = 0
        dut.MI_DRDY.value = 0
        dut.MI_DRD.value = 0

        cocotb.start_soon(self._run())

    # ------------------------------------------------------------------ setup

    def set_ready(self, pattern: Iterator[bool]) -> None:
        self._ready = pattern

    def set_ready_rate(self, rate: float) -> None:
        self.set_ready(random_ready(rate, random.Random(self.rng.random())) if rate > 0 else always(True))

    def set_latency(self, minimum: int, maximum: Optional[int] = None) -> None:
        """Read latency in cycles, drawn uniformly from <minimum, maximum> for every read."""
        top = minimum if maximum is None else maximum
        rng = random.Random(self.rng.random())
        self._latency = lambda: rng.randint(minimum, top)

    def word_address(self, addr: int) -> int:
        return addr // self.word_bytes

    def read_word(self, word_address: int) -> bytes:
        return self.memory.get(word_address, default_content(word_address, self.word_bytes))

    def clear(self) -> None:
        """Drops recorded traffic and pending responses, e.g. after a reset of the DUT."""
        self.baseline = dict(self.memory)
        self.requests.clear()
        self.read_data.clear()
        self.violations.clear()
        self.same_cycle_responses = 0
        self._pending.clear()
        self._previous = None

    @property
    def busy(self) -> bool:
        return bool(self._pending)

    # ------------------------------------------------------------------ model

    def _violation(self, message: str) -> None:
        text = f"cycle {self._cycle}: {message}"
        self.violations.append(text)
        self.log.error("MI protocol: %s", text)

    async def _run(self) -> None:
        edge = RisingEdge(self.clock)

        while True:
            await edge
            self._cycle += 1
            self._sample()

            await ReadWrite()
            self._drive()

    def _sample(self) -> None:
        """Evaluates the cycle that has just ended (values sampled at the rising edge)."""
        dut = self.dut
        in_reset = bool(dut.RESET.value)

        rd = dut.MI_RD.value
        wr = dut.MI_WR.value
        ardy = bool(dut.MI_ARDY.value)
        drdy = bool(dut.MI_DRDY.value)

        if in_reset:
            self._pending.clear()
            self._previous = None
            return

        if not (rd.is_resolvable and wr.is_resolvable):
            if self.checking:
                self._violation(f"MI_RD/MI_WR not resolvable ({rd}/{wr})")
            return

        rd_b, wr_b = bool(rd), bool(wr)

        # The response of this cycle was consumed by the DUT.
        if drdy:
            if self._drdy_head:
                self.read_data.append(self._pending.popleft().data)
            elif self._same_cycle is not None:
                self.read_data.append(self._same_cycle)
                if rd and ardy:
                    self.same_cycle_responses += 1

        if not (rd_b or wr_b):
            self._previous = None
            return

        if rd_b and wr_b:
            self._violation("MI_RD and MI_WR asserted together")

        addr_v, be_v, dwr_v = dut.MI_ADDR.value, dut.MI_BE.value, dut.MI_DWR.value

        if self.checking:
            if not addr_v.is_resolvable:
                self._violation(f"MI_ADDR not resolvable during a request: {addr_v}")
            if not be_v.is_resolvable:
                self._violation(f"MI_BE not resolvable during a request: {be_v}")
            if wr_b and not dwr_v.is_resolvable:
                self._violation(f"MI_DWR not resolvable during a write: {dwr_v}")
            if rd_b and be_v.is_resolvable and be_v.to_unsigned() != self.be_all:
                self._violation(f"MI_BE of a read is {be_v}, expected all ones")
            if self._pending and not self._drdy_head:
                self._violation("new MI request while a read response is still pending")

        addr = addr_v.to_unsigned() if addr_v.is_resolvable else 0
        be = be_v.to_unsigned() if be_v.is_resolvable else 0
        dwr = dwr_v.to_unsigned().to_bytes(self.word_bytes, "little") if wr_b and dwr_v.is_resolvable else b""

        current = (rd_b, wr_b, addr, be, dwr)
        if self.checking and self._previous is not None and self._previous != current:
            self._violation(f"MI request changed before it was accepted: {self._previous} -> {current}")

        if not ardy:
            self._previous = current
            return

        self._previous = None
        self.requests.append(MiRequest(write=wr_b, addr=addr, data=dwr, be=be, cycle=self._cycle))

        word = self.word_address(addr)
        if wr_b:
            old = bytearray(self.read_word(word))
            for lane in range(self.word_bytes):
                if be >> lane & 1:
                    old[lane] = dwr[lane]
            self.memory[word] = bytes(old)
        elif self._same_cycle is None:
            self._pending.append(_PendingRead(due=self._cycle - 1 + self._planned_latency, data=self.read_word(word)))

    def _drive(self) -> None:
        """Drives MI_ARDY, MI_DRDY and MI_DRD for the cycle that has just started."""
        dut = self.dut
        self._drdy_head = False
        self._same_cycle = None

        if bool(dut.RESET.value):
            dut.MI_ARDY.value = 0
            dut.MI_DRDY.value = 0
            return

        ardy = next(self._ready)
        dut.MI_ARDY.value = int(ardy)

        if self._pending and self._pending[0].due <= self._cycle:
            self._drdy_head = True
            dut.MI_DRDY.value = 1
            dut.MI_DRD.value = int.from_bytes(self._pending[0].data, "little")
            return

        self._planned_latency = self._latency()

        rd = dut.MI_RD.value
        addr = dut.MI_ADDR.value
        if (ardy and self._planned_latency == 0 and not self._pending and rd.is_resolvable and bool(rd)
                and addr.is_resolvable):
            # The DUT samples MI_DRDY together with MI_ARDY in the request cycle.
            self._same_cycle = self.read_word(self.word_address(addr.to_unsigned()))
            dut.MI_DRDY.value = 1
            dut.MI_DRD.value = int.from_bytes(self._same_cycle, "little")
            return

        if self._planned_latency == 0:
            self._planned_latency = 1
        dut.MI_DRDY.value = 0
        # Garbage on MI_DRD outside MI_DRDY catches a DUT that samples it at the wrong time.
        dut.MI_DRD.value = self.rng.getrandbits(8 * self.word_bytes)
