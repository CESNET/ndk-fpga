# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>


from cocotb_bus.monitors import BusMonitor
from cocotb.triggers import RisingEdge

from transaction import IdMemTr, TagMemTr


class BaseMemMonitor(BusMonitor):
    """Base monitor for the IDMEM and TAGMEM interfaces of the PPR Request Processor."""

    _signals = ["vld"]
    _optional_signals = []

    def __init__(self, entity, name, clock, tr_type, array_idx=None) -> None:
        super().__init__(entity, name, clock, array_idx=array_idx)

        self.__tr_type = tr_type
        self.__os = [s for s in self._optional_signals if hasattr(self.bus, s)]
        self.__item_cnt = 0
        self.__items = len(self.bus.vld)
        self.__item_widths = self._get_item_widths()

    @property
    def os(self) -> list:
        """A list of names of optional signals that are on the bus
        (filtered version of the _optional_signals).
        """
        return self.__os

    @property
    def item_cnt(self) -> int:
        """The number of currently proccessed MVB transactions."""
        return self.__item_cnt

    @property
    def items(self) -> int:
        """The number of MVB items in word."""
        return self.__items

    @property
    def item_widths(self) -> dict:
        """A dictionary where "keys" are the names of the optional signals on the bus
        (items of the "os" list) and "values" are their respective widths.
        """
        return self.__item_widths

    def _get_item_widths(self) -> dict:
        """Make a dictionary of all optional signals on the bus and the width of each one's item."""
        return {s: len(getattr(self.bus, s)) // self.__items for s in self.__os}

    def _is_valid_word(self, signal_src_rdy, signal_dst_rdy) -> bool:
        """Checks if the received word is valid transaction."""
        if signal_dst_rdy is None:
            return (signal_src_rdy.value == 1)
        else:
            return (signal_src_rdy.value == 1) and (signal_dst_rdy.value == 1)

    def recv_tr(self, vld):
        data_dict_word = {}
        data_dict_items = {}
        for s in self.__os:
            # Splitting the word into a list of items by masking and shifting
            data_dict_word[s] = getattr(self.bus, s).value.to_unsigned()
            data_mask = 2**self.__item_widths[s] - 1
            data_dict_items[s] = []
            for i in range(self.__items):
                data_dict_items[s].append(data_dict_word[s] & data_mask)
                data_dict_word[s] >>= self.__item_widths[s]

        self.log.debug(f"Got signals: vld={vld}, data={data_dict_items}")
        for i in range(self.__items):
            if (vld & 1):
                tr = self.__tr_type
                for s in self.__os:
                    if hasattr(tr, s):
                        setattr(tr, s, data_dict_items[s][i])
                self._recv(tr)
                self.log.debug(f"Monitor received transaction: {tr}")
            vld >>= 1

    async def _monitor_recv(self) -> None:
        """Receive function used with cocotb testbench."""
        clk_re = RisingEdge(self.clock)

        while True:
            await clk_re

            if self.in_reset:
                continue

            if vld := self.bus.vld.value.to_unsigned() > 0:
                self.__item_cnt += self.bus.vld.value.count("1")
                self.recv_tr(vld)


class IdMemMonitor(BaseMemMonitor):
    _optional_signals = ["id", "addr", "words", "eof_pos", "tag_cnt"]

    def __init__(self, entity, name, clock, array_idx=None) -> None:
        super().__init__(entity, name, clock, tr_type=IdMemTr(), array_idx=array_idx)


class TagMemMonitor(BaseMemMonitor):
    _optional_signals = ["tag", "addr", "id", "firstib"]

    def __init__(self, entity, name, clock, array_idx=None) -> None:
        super().__init__(entity, name, clock, tr_type=TagMemTr(), array_idx=array_idx)
