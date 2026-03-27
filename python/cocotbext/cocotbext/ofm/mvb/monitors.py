# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <ondrejschwarz@cesnet.cz>
#            Daniel Kondys <kondys@cesnet.cz>


from cocotb.handle import ModifiableObject
from cocotb_bus.monitors import BusMonitor
from cocotb.triggers import RisingEdge

from .transaction import MvbTransaction, MvbTrClassic


class MVBMonitor(BusMonitor):
    """
    Master monitor intended for monitoring the MVB bus.

    In case your MVB bus contains optional signals different from those defined in the
    _optional_signals class attribute, please create your own monitor class inheriting from this
    one with your custom _optional_signals list.

    Atributes:
        _tr_type: specifies the type of transactions that are output from the Monitor.
                  Options: bytes (depracated - supported only for backward compatibility),
                  a subclass of the MvbTransaction class.
    """

    _signals = ["vld", "src_rdy", "dst_rdy"]
    _optional_signals = ["data", "meta", "addr", "discard", "length", "match"]

    def __init__(self, entity, name, clock, array_idx=None, tr_type=bytes) -> None:
        super().__init__(entity, name, clock, array_idx=array_idx)

        self.__os = [s for s in self._optional_signals if hasattr(self.bus, s)]
        self.__item_cnt = 0
        self.__items = len(self.bus.vld)
        self.__bus_isarray = not isinstance(getattr(self.bus, self.__os[0]), ModifiableObject)
        self.__item_widths = self._get_item_widths()
        self.__item_width = sum(self.__item_widths.values())
        self.__tr_type = tr_type

        if self.__tr_type == bytes:
            self._recv_method = self.recv_bytes
        elif issubclass(self.__tr_type, MvbTransaction):
            self._recv_method = self.recv_mvb_tr
        else:
            raise NotImplementedError(f"Transaction type ({self.__tr_type}) is not supported!")

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

    @property
    def item_width(self) -> int:
        """The width of a full item (all data items), i.e., sum of item_widths of all optional signals.
        Needed only for the compatibility with the ThroughputProbe.
        """
        return self.__item_width

    @property
    def bus_isarray(self) -> bool:
        """Indicates whether the bus is a vector or an array."""
        return self.__bus_isarray

    def _get_item_widths(self) -> dict:
        """Make a dictionary of all optional signals on the bus and the width of each one's item."""
        if self.__bus_isarray:
            return {s: len(getattr(self.bus, s)[0]) for s in self.__os}
        else:
            return {s: len(getattr(self.bus, s)) // self.__items for s in self.__os}

    def _is_valid_word(self, signal_src_rdy, signal_dst_rdy) -> bool:
        """Checks if the received word is valid transaction."""
        if signal_dst_rdy is None:
            return (signal_src_rdy.value == 1)
        else:
            return (signal_src_rdy.value == 1) and (signal_dst_rdy.value == 1)

    def recv_bytes(self, vld):
        data_val = getattr(self.bus, self.__os[0]).value
        data_val.big_endian = False
        data_bytes = data_val.buff
        # Number of bytes in each Item (= length of each data slice)
        item_bytes = next(iter(self.__item_widths.values())) // 8
        for i in range(self.__items):
            # Mask and shift the Valid signal per each Item
            if (vld & 1):
                # Getting the data slice (Item) from the "bytes" transaction
                data_b = data_bytes[i*item_bytes : (i+1)*item_bytes]
                # Converting the data slice (Item) to the MvbTrClassic object
                mvb_tr = MvbTrClassic.from_bytes(data_b)
                self._recv(mvb_tr)
            vld >>= 1

    def recv_mvb_tr(self, vld):
        data_dict_word = {}
        data_dict_items = {}
        for s in self.__os:
            if self.__bus_isarray:
                data_dict_word[s] = getattr(self.bus, s)
                data_dict_items[s] = [data_dict_word[s][i].value.integer for i in range(len(data_dict_word[s]))]

            else: # Splitting the word into a list of items by masking and shifting
                data_dict_word[s] = getattr(self.bus, s).value
                data_mask = 2**self.__item_widths[s] - 1
                data_dict_items[s] = []
                for i in range(self.__items):
                    data_dict_items[s].append(data_dict_word[s] & data_mask)
                    data_dict_word[s] >>= self.__item_widths[s]

        for i in range(self.__items):
            if (vld & 1):
                kwargs = {
                    s: data_dict_items[s][i]
                    for s in self.__os
                    if s in data_dict_items
                }

                mvb_tr = self.__tr_type(**kwargs)
                self._recv(mvb_tr)
            vld >>= 1

    async def _monitor_recv(self) -> None:
        """Receive function used with cocotb testbench."""
        # Avoid spurious object creation by recycling
        clk_re = RisingEdge(self.clock)

        while True:
            await clk_re

            if self.in_reset:
                continue

            if self._is_valid_word(self.bus.src_rdy, self.bus.dst_rdy):
                vld = self.bus.vld.value.integer
                self.__item_cnt += self.bus.vld.value.binstr.count("1") # Python 3.9 and below
                # self.__item_cnt += vld.bit_count # from Python 3.10

                self._recv_method(vld)
