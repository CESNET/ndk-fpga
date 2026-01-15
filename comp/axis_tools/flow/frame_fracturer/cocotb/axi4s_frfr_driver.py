# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>

import copy

from cocotbext.ofm.base.drivers import BusDriver
from cocotbext.ofm.axi4stream.transaction import Axi4StreamBaseTransaction
from cocotbext.ofm.base.transaction import IdleTransaction
from cocotbext.ofm.utils.math import ceildiv, bitmask
from cocotb.queue import Queue
from typing import Any


class Axi4sFrfrDriver(BusDriver):
    """Drives the RX_AXI and RX_FRACTURE ports ofr the AXIS_FRAME_FRACTURER."""

    _signals = ["AXI_TVALID", "AXI_TREADY"]
    _optional_signals = ["AXI_TDATA", "AXI_TLAST", "AXI_TKEEP", "FRACTURE_EN", "FRACTURE_OFFSET"]

    def __init__(self, entity, name, clock, array_idx=None) -> None:
        super().__init__(entity, name, clock, array_idx=array_idx)

        self._data = {s: 0 for s in Axi4sFrfrDriver._optional_signals}
        self._clear_control_signals()
        self._propagate_control_signals()
        self._end_len = 0

    def _split_frame(self, transaction: Axi4StreamBaseTransaction) -> Queue:
        """
        Splits a descendant of Axi4StreamBaseTransaction into words and returns them as a Queue of dictionaries.
        """
        transaction = copy.copy(transaction)
        tr_data = transaction.TDATA # All bytes of the frame, to be split
        fracture_en = transaction.FRACTURE_EN # List of fractures (one item per word)
        fracture_offset = transaction.FRACTURE_OFFSET # List of fractures (one item per word)
        split_frame_queue = Queue()

        word_width = len(self.bus.AXI_TDATA) // 8 # Bus word width in bytes
        tr_len = len(tr_data) # Transaction length in bytes
        word_cnt = ceildiv(word_width, tr_len) # The amount of words the transaction will strech over
        if word_cnt != len(fracture_en):
            raise RuntimeError

        for i in range(word_cnt):
            trans_dict = dict()
            trans_dict["AXI_TDATA"] = int.from_bytes(tr_data[:word_width], "little")
            if tr_len >= word_width:
                trans_dict["AXI_TKEEP"] = bitmask(word_width)
            else:
                trans_dict["AXI_TKEEP"] = bitmask(tr_len)
                self._end_len = tr_len
            trans_dict["AXI_TLAST"] = 1 if tr_len <= word_width else 0
            trans_dict["FRACTURE_EN"] = fracture_en[i]
            trans_dict["FRACTURE_OFFSET"] = fracture_offset[i]

            split_frame_queue.put_nowait(trans_dict)
            tr_data = tr_data[word_width:]
            tr_len -= word_width

        return split_frame_queue

    def _clear_control_signals(self) -> None:
        """Clears values of control signals. In most cases, self._tvalid = 0 is used instead."""
        for sig in self._data:
            self._data[sig] = 0
        self._tvalid = 0

    def _propagate_control_signals(self) -> None:
        """Writes value of control signals onto the AXI bus."""

        for sig, val in self._data.items():
            getattr(self.bus, sig).value = val

        self.bus.AXI_TVALID.value = self._tvalid

    async def _move_word(self) -> None:
        """Sends AXI word to the driven bus if possible and clears the word."""

        self._propagate_control_signals()

        await self._clk_re
        while self.bus.AXI_TREADY.value != 1:
            self._idle_gen.put(self._idle_tr, **{"items": len(self.bus.AXI_TDATA)//8})
            await self._clk_re

        self._tvalid = 0

    async def _driver_send(self, transaction: dict[str, int], sync: bool = True, **kwargs: Any) -> None:
        """Writes real and idle transaction to the bus."""
        # handle idle transaction - currently not supported
        if isinstance(transaction, IdleTransaction):
            self._tvalid = 0
            await self._move_word()
        # handle valid transaction
        else:
            for sig in self._data:
                self._data[sig] = transaction[sig]
            self._tvalid = 1
            await self._move_word()

        if self._data["AXI_TLAST"] == 1:
            self._idle_gen.put(transaction, **{"items": self._end_len, "end": True})
            self._end_len = 0
        else:
            self._idle_gen.put(transaction, **{"items": len(self.bus.AXI_TDATA)//8, "end": False})

    async def _send_thread(self) -> None:
        while True:
            while not self._sendQ:
                self._pending.clear()
                await self._pending.wait()

            while self._sendQ:
                transaction, callback, event, kwargs = self._sendQ.popleft()

                if isinstance(transaction, Axi4StreamBaseTransaction):
                    # splits transaction into words in a queue
                    trans_queue = self._split_frame(transaction)
                elif isinstance(transaction, dict):
                    # creates a queue and puts only one word into it (for backwards compatibility)
                    trans_queue = Queue()
                    trans_queue.put_nowait(transaction)
                else:
                    raise TypeError("Unsupported transaction type passed to _send_thread of Axi4sFrfrDriver.")

                # processing all words of the transaction
                while not trans_queue.empty():
                    transaction = trans_queue.get_nowait()

                    # send idle transactions inbetween words
                    for _ in range(self._idle_gen.get(transaction)):
                        await self._send(self._idle_tr, callback=None, event=event, sync=False, **kwargs)

                    await self._send(transaction, callback=None, event=event, sync=False, **kwargs)

                if event:
                    event.set()
                if callback:
                    callback(transaction)

            await self._move_word()
            await self._move_word()
