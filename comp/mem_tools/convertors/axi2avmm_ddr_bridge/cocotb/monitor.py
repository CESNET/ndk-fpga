# monitor.py: Monitor of the Avalon-MM side of the bridge
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author: David Beneš <benes@dyna-nic.com>, 2026
#
# SPDX-License-Identifier: BSD-3-Clause

"""Monitor of the Avalon-MM side of the bridge.

It reconstructs what the master asked for: which word has to end up at which
byte address on the AXI side, and which words a read request has to return. The
reconstruction follows the Avalon-MM specification only, it does not model the
bridge, so its output is a reference the DUT is compared against.
"""

from dataclasses import dataclass
from typing import Any, Optional

import cocotb
from cocotb.triggers import ReadOnly, RisingEdge

from signals import bit, uint


@dataclass
class AmmWriteBeat:
    """One write data word accepted on the Avalon-MM interface."""
    word_address : int
    byte_address : int
    data         : bytes


class AmmMonitor:
    def __init__(self, dut: Any, clock: Any, reset: Any, word_bytes: int, model: Any) -> None:
        self.dut = dut
        self.clock = clock
        self.reset = reset
        self.word_bytes = word_bytes
        self.model = model
        self.log = cocotb.log

        self.write_beats : list[AmmWriteBeat] = []
        self.read_data : list[bytes] = []

        # word addresses the accepted read requests are expected to return, in order
        self.expected_read_words : list[int] = []

        # contents of those words at the moment the request was accepted
        self.expected_read_data : list[bytes] = []

        self._burst_base : Optional[int] = None
        self._burst_index = 0
        self._burst_count = 0

        self._enabled = False

        cocotb.start_soon(self._sample_loop())

    def enable(self, enabled: bool = True) -> None:
        self._enabled = enabled

    def _handle_write(self) -> None:
        dut = self.dut

        # a new burst starts with the first beat after the previous one finished;
        # only that beat carries a valid address and burstcount
        if self._burst_base is None:
            self._burst_base = uint(dut.AMM_ADDRESS)
            self._burst_count = uint(dut.AMM_BURST_COUNT)
            self._burst_index = 0

            if self._burst_base is None or self._burst_count is None:
                self.log.error("Avalon-MM write accepted with an undefined address or burstcount")
                self._burst_base = None
                return

        word_address = self._burst_base + self._burst_index
        data = uint(dut.AMM_WRITE_DATA)

        if data is None:
            self.log.error("Avalon-MM write beat accepted with undefined write data at word %#x", word_address)
            data = 0

        self.write_beats.append(AmmWriteBeat(word_address, word_address * self.word_bytes,
                                             data.to_bytes(self.word_bytes, "little")))

        self._burst_index += 1
        if self._burst_index >= self._burst_count:
            self._burst_base = None

    def _handle_read(self) -> None:
        address = uint(self.dut.AMM_ADDRESS)
        burst_count = uint(self.dut.AMM_BURST_COUNT)

        if address is None or burst_count is None:
            self.log.error("Avalon-MM read accepted with an undefined address or burstcount")
            return

        # Snapshot now, not when the test compares: a later write to the same
        # word must not change what this read owed.
        for word in range(address, address + burst_count):
            self.expected_read_words.append(word)
            self.expected_read_data.append(self.model.read(word))

    async def _sample_loop(self) -> None:
        dut = self.dut

        while True:
            # Reading right after the edge is not portable: some simulators have
            # propagated its values and some have not. ReadOnly runs once the
            # timestep has settled, so every simulator reads the same cycle.
            await RisingEdge(self.clock)
            await ReadOnly()

            if bit(self.reset):
                self._burst_base = None
                continue

            if not self._enabled:
                continue

            ready = bit(dut.AMM_READY)

            if ready and bit(dut.AMM_WRITE):
                self._handle_write()

            if ready and bit(dut.AMM_READ):
                self._handle_read()

            if bit(dut.AMM_READ_DATA_VALID):
                data = uint(dut.AMM_READ_DATA)

                if data is None:
                    self.log.error("Avalon-MM read data beat is undefined")
                    data = 0

                self.read_data.append(data.to_bytes(self.word_bytes, "little"))
