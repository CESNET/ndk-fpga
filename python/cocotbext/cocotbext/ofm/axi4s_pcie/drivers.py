# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>

import copy
from typing import Any

from cocotbext.ofm.base.drivers import BusDriver
from cocotbext.ofm.base.transaction import IdleTransaction
from cocotbext.ofm.utils import concat, byte_deserialize
from cocotbext.ofm.utils.math import bitmask
from cocotbext.ofm.pcie.PcieHeaders import RCHeader, CQHeader, RCUser


class Axi4sPcieDriverMaster(BusDriver):
    """
    Unified driver for PCIe AXI4-Stream RC (Completion) and CQ (Request) interfaces.

    Automatically detects transaction type based on header class:
    - RCHeader -> RC transaction (completion from requester)
    - CQHeader -> CQ transaction (request from completer)

    Transaction formats:
    - RC: (rc_hdr, data) - driver calculates RCUser automatically
    - CQ: (cq_hdr, data, cq_user) - completer provides CQUser with address alignment info

    For CQ transactions, header is only included in the first word;
    subsequent words use empty header. For RC, header is always present.
    """

    _signals = ["VALID", "READY", "DATA", "KEEP", "USER"]

    def __init__(self, entity, name, clock, array_idx=None):
        super().__init__(entity, name, clock, array_idx=array_idx)

        for sig in self._signals:
            if sig != "READY":
                getattr(self.bus, sig).setimmediatevalue(0)

    def _clear_control_signals(self):
        """Clear control signals when sending idle."""
        self.bus.VALID.value = 0

    def _prep_rc_words(self, rc_hdr, data, bus_width):
        """Convert RC (hdr, data) to bus words."""
        dwords_per_word = bus_width // 32

        # RC: header always present (3 DWs)
        dword_count = rc_hdr.dword_count + 3

        user = RCUser()
        user.sop = 1
        user.eop = 0
        user.eop0 = dword_count - 1

        # PCIe header prepended to data
        tdata = concat(
            [(rc_hdr.serialize(), len(rc_hdr))]
            + [(byte_deserialize(data), len(data) * 8)]
        )

        while dword_count > 0:
            tkeep = bitmask(dwords_per_word)
            if dword_count <= dwords_per_word:
                user.eop = 1
                user.eop0 = dword_count - 1
                tkeep = bitmask(dword_count)

            word = {
                "DATA": tdata & bitmask(bus_width),
                "USER": user.serialize(),
                "KEEP": tkeep,
            }
            yield word

            user.sop = 0
            tdata >>= bus_width
            dword_count -= dwords_per_word

        return word

    def _prep_cq_words(self, cq_hdr, data, cq_user, bus_width):
        """
        Convert CQ (hdr, data, user) to bus words.

        CQ format: header only in first word, then empty header + remaining data.
        Data can be bytes or list of bytes (already padded/aligned by completer).
        """
        # Convert data to list of bytes if needed
        if isinstance(data, bytes):
            data_bytes = list(data)
        elif isinstance(data, list):
            data_bytes = data
        else:
            raise TypeError(f"Data must be bytes or list, got {type(data)}")

        hdr_bits = len(cq_hdr)
        hdr_bytes = hdr_bits // 8
        hdr_serialized = cq_hdr.serialize()

        # First word: header + some data bytes
        # Calculate how many data bytes fit in first word after header
        first_word_data_bytes = min(bus_width // 8 - hdr_bytes, len(data_bytes))

        # Build first word: header + data bytes
        first_word_data = data_bytes[:first_word_data_bytes]
        tdata = concat(
            [(hdr_serialized, hdr_bits)]
            + list(zip(first_word_data, [8] * len(first_word_data)))
        )

        # Calculate TKEEP: header dwords + data dwords
        first_word_dwords = (hdr_bits + len(first_word_data) * 8 + 31) // 32
        tkeep = bitmask(first_word_dwords)

        # Set EOP if this is the last word
        remaining_data = data_bytes[first_word_data_bytes:]
        if len(remaining_data) == 0:
            cq_user.eop0 = 1

        word = {
            "DATA": tdata & bitmask(bus_width),
            "USER": cq_user.serialize(),
            "KEEP": tkeep,
        }
        yield word

        cq_user.sop0 = 0
        remaining_bytes = remaining_data

        while len(remaining_bytes) > 0:
            # Calculate how many bytes fit in this word (full word, no header)
            word_data_bytes = min(bus_width // 8, len(remaining_bytes))
            word_data = remaining_bytes[:word_data_bytes]

            tdata = concat(list(zip(word_data, [8] * len(word_data))))
            word_dwords = (len(word_data) * 8 + 31) // 32
            tkeep = bitmask(word_dwords)

            # Set EOP if this is the last word
            if len(remaining_bytes) <= word_data_bytes:
                cq_user.eop0 = 1
            else:
                cq_user.eop0 = 0

            word = {
                "DATA": tdata & bitmask(bus_width),
                "USER": cq_user.serialize(),
                "KEEP": tkeep,
            }
            yield word
            remaining_bytes = remaining_bytes[word_data_bytes:]

    def _prep_words(self, hdr, data, user=None):
        """
        Convert (hdr, data) or (hdr, data, user) transaction to bus words.

        Automatically detects RCHeader vs CQHeader and routes to appropriate method.
        """
        words = []
        data_width = len(self.bus.DATA)
        if isinstance(hdr, RCHeader):
            if user is not None:
                raise ValueError("RC transactions do not accept user parameter")
            for word in self._prep_rc_words(hdr, data, data_width):
                words.append(word)
        elif isinstance(hdr, CQHeader):
            if user is None:
                raise ValueError("CQ transactions require CQUser parameter")
            for word in self._prep_cq_words(hdr, data, user, data_width):
                words.append(word)
        else:
            raise TypeError(f"Header must be RCHeader or CQHeader, got {type(hdr).__name__}")
        return words

    async def _write_word(self, word, sync=True):
        """Drive one word onto the bus, wait for READY."""
        word = copy.copy(word)

        self.bus.VALID.value = 1
        for signal, value in word.items():
            getattr(self.bus, signal).value = value

        await self._clk_re
        while not self.bus.READY.value:
            await self._clk_re

        self._clear_control_signals()

    async def _driver_send(self, transaction: Any, sync: bool = True, **kwargs: Any):
        """
        Handle idle or PCIe transaction.

        Transaction formats:
        - IdleTransaction: idle cycle
        - (hdr, data): RC transaction (auto-detected from RCHeader)
        - (hdr, data, user): CQ transaction (CQHeader + CQUser)
        """
        if isinstance(transaction, IdleTransaction):
            self._clear_control_signals()
            await self._clk_re
            return

        if isinstance(transaction, tuple):
            if len(transaction) == 2:
                hdr, data = transaction
                user = None
            elif len(transaction) == 3:
                hdr, data, user = transaction
            else:
                raise ValueError(
                    f"Transaction must be (hdr, data) or (hdr, data, user), got tuple of length {len(transaction)}"
                )
        else:
            raise TypeError(f"Transaction must be tuple or IdleTransaction, got {type(transaction)}")

        words = self._prep_words(hdr, data, user)

        for word in words:
            # Insert idles between words
            for _ in range(self._idle_gen.get(word)):
                await self._driver_send(self._idle_tr, sync=False, **kwargs)

            await self._write_word(word, sync=False)


class Axi4sPcieDriverSlave(BusDriver):
    _signals = ["VALID", "READY"]

    def __init__(self, entity, name, clock, array_idx=None):
        BusDriver.__init__(self, entity, name, clock, array_idx=array_idx)

        self.bus.READY.setimmediatevalue(1)
