# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025-2026 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#            Ondrej Schwarz <ondrejschwarz@cesnet.cz>

import copy

from cocotbext.ofm.base.drivers import BusDriver
from cocotbext.ofm.axi4stream.transaction import Axi4StreamBaseTransaction
from cocotbext.ofm.base.transaction import IdleTransaction
from cocotbext.ofm.utils.math import ceildiv, bitmask
from dataclasses import asdict
from cocotb.queue import Queue
from cocotb.types import LogicArray
#from cocotb.handle import Immediate
from typing import Any


class Axi4StreamMaster(BusDriver):
    _signals = ["TVALID", "TREADY", "TDATA"]
    _optional_signals = ["TLAST", "TSTRB", "TKEEP", "TID", "TDEST", "TUSER", "SEL"]

    def __init__(self, entity, name, clock, array_idx=None):
        super().__init__(entity, name, clock, array_idx=array_idx)

        ms, os = self._signals, self._optional_signals
        self.all_signals = ms | os if isinstance(ms, dict) else ms + os
        for s in self.all_signals:
            if hasattr(self.bus, s) and s not in ["TREADY"]:
                signal = getattr(self.bus, s)
                length = len(signal.value)
                value = 2 ** length - 1 if s in ["TSTRB", "TKEEP"] else 0

                #signal.set(Immediate(value))
                signal.setimmediatevalue(value)

    def _clear_control_signals(self):
        for name in self.all_signals:
            if hasattr(self.bus, name) and name != "TREADY":
                signal = getattr(self.bus, name)

                if name == "TVALID":
                    signal.value = 0
                else:
                    signal.value = LogicArray("X" * len(signal))

    def _split_frame(self, transaction: Axi4StreamBaseTransaction) -> Queue:
        """
        Splits a descendant of Axi4StreamBaseTransaction into words and returns them as a Queue of dictionaries.
        """
        transaction = copy.copy(transaction)
        split_frame_queue = Queue()

        data_width = len(self.bus.TDATA) // 8
        data_len   = len(transaction.TDATA)
        word_cnt = ceildiv(data_width, data_len)

        for i in range(word_cnt, 0, -1):
            trans_dict = dict()

            # generating TKEEP and TLAST (will be ovewritten if it's specified in the transaction)
            if hasattr(self.bus, "TKEEP"):
                trans_dict["TKEEP"] = bitmask(data_width) if len(transaction.TDATA) >= data_width else bitmask(len(transaction.TDATA))
            if hasattr(self.bus, "TLAST"):
                trans_dict["TLAST"] = 1 if len(transaction.TDATA) <= data_width else 0
            if hasattr(self.bus, "SEL"):
                trans_dict["SEL"] = transaction.SEL

            for name, value in asdict(transaction).items():
                if hasattr(self.bus, name):
                    if isinstance(value, bytes):
                        width = len(getattr(self.bus, name)) // 8
                        trans_dict[name] = int.from_bytes(value[:width], "little")
                        setattr(transaction, name, value[width:])
                    elif isinstance(value, int):
                        width = len(getattr(self.bus, name))
                        mask  = bitmask(width) << (i-1)*width
                        trans_dict[name] = (value & mask) >> (i-1)*width
                    else:
                        raise TypeError(f"Unsupported type of {name} in transaction passed to _driver_send of Axi4StreamMaster.")

            split_frame_queue.put_nowait(trans_dict)

        return split_frame_queue

    async def write(self, data: dict[str, int], sync=True):
        """
        Writes valid transaction represented as a dictionary of intetegers to the bus.
        """
        data = copy.copy(data)

        if sync:
            await self._clk_re

        self.bus.TVALID.value = 1

        for signal, value in data.items():
            getattr(self.bus, signal).value = value

        await self._clk_re
        while hasattr(self.bus, "TREADY") and not self.bus.TREADY.value:
            await self._clk_re

        self.bus.TVALID.value = 0
        self._clear_control_signals()

    async def _driver_send(self, transaction: dict[str, int], sync: bool = True, **kwargs: Any):
        """
        Writes idle transaction to the bus or passes valid transaction to the write method.
        """

        # handle idle transaction
        if isinstance(transaction, IdleTransaction):
            self._clear_control_signals()
            await self._clk_re

        # handle valid transaction
        else:
            await self.write(transaction, sync=sync)

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
                    raise TypeError("Unsupported transaction type passed to _send_thread of Axi4DriverMaster.")

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


class Axi4StreamSlave(BusDriver):
    _signals = ["TVALID", "TREADY"]

    def __init__(self, entity, name, clock, array_idx=None):
        super().__init__(entity, name, clock, array_idx=array_idx)

        #self.bus.TREADY.set(Immediate(1))
        self.bus.TREADY.setimmediatevalue(1)
