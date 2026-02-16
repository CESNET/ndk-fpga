# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#            Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from cocotb_bus.monitors import BusMonitor
from cocotb.triggers import RisingEdge
from cocotbext.ofm.utils.binary import Binary, BinaryVector
from cocotbext.ofm.mfb.utils import get_mfb_params
from cocotbext.ofm.mfb.transaction import MfbTransaction
from math import log2
from copy import copy

# NOTE remove line 48 while/after reimplementing MFB driver !!!


class MFBProtocolError(Exception):
    pass


class MFBMonitor(BusMonitor):
    """
    Monitor for the MFB bus.

    Args:
        trans_type: The desired type for the transactions returned by the monitor.
                    Defaults to `bytes` for backward compatibility.
                    Consider using a child class of `MfbTransaction` for more structured data.

        meta_valid_with: Specifies which signal indicates the validity of metadata
                         if the 'meta' or similar signal is present. Must be either "sof" (start of frame)
                         or "eof" (end of frame).
    """

    _signals = ["data", "sof_pos", "eof_pos", "sof", "eof", "src_rdy", "dst_rdy"]
    _optional_signals = ["meta"]

    def __init__(self, entity, name, clock, array_idx=None, mfb_params=None, trans_type: MfbTransaction | bytes = bytes):
        super().__init__(entity, name, clock, array_idx=array_idx)

        self._regions, self._region_size, self._block_size, self._item_width, self._meta_width, self._os_vld_with = get_mfb_params(
            self.bus, mfb_params
        )
        self._region_items = self._region_size * self._block_size
        self._os = [s for s in self._optional_signals if hasattr(self.bus, s)]
        self._os_widths = {s: len(getattr(self.bus, s)) // self._regions for s in self._os}

        self._item_width = 8 # remove this line while/after reimplementing MFB driver!!!

        self._trans_type  = trans_type
        self._transaction = MfbTransaction() if self._trans_type is bytes else trans_type()

        self._data    = BinaryVector(item_count=self._regions, item_bits=self._region_items*self._item_width, endian="little")
        self._sof_pos = BinaryVector(item_count=self._regions, item_bits=int(log2(self._region_size)))
        self._eof_pos = BinaryVector(item_count=self._regions, item_bits=int(log2(self._region_size*self._block_size)))
        self._sof     = Binary(bits=self._regions)
        self._eof     = Binary(bits=self._regions)
        self._os_data = {s: BinaryVector(item_count=self._regions, item_bits=self._os_widths[s]) for s in self._os}

        self.frame_cnt = 0
        self.item_cnt  = 0

    def _is_valid_word(self, signal_src_rdy, signal_dst_rdy):
        if signal_dst_rdy is None:
            return (signal_src_rdy.value == 1)
        else:
            return (signal_src_rdy.value == 1) and (signal_dst_rdy.value == 1)

    def _read_control_signals(self):
        self._data.value    = self.bus.data.value.integer
        self._sof_pos.value = self.bus.sof_pos.value.integer
        self._eof_pos.value = self.bus.eof_pos.value.integer
        self._sof.value     = self.bus.sof.value.integer
        self._eof.value     = self.bus.eof.value.integer

        for s in self._os:
            self._os_data[s].value = getattr(self.bus, s).value.integer

    def _recv_trans(self):
        self.log.debug(f"received transaction: {self._transaction}")

        if self._trans_type is bytes:
            self._recv(self._transaction.data)
        else:
            self._recv(copy(self._transaction))

    async def _monitor_recv(self):
        clk_re = RisingEdge(self.clock)

        in_frame = False

        while True:
            await clk_re

            if self.in_reset:
                continue

            if self._is_valid_word(self.bus.src_rdy, self.bus.dst_rdy):
                self._read_control_signals()

                for r in range(self._regions):
                    sof = self._sof[r].int
                    eof = self._eof[r].int

                    sof_pos = self._sof_pos[r].int if sof else 0
                    eof_pos = self._eof_pos[r].int if eof else 0

                    pkt_start = sof_pos * self._block_size * self._item_width
                    pkt_end   = (eof_pos + 1) * self._item_width

                    if in_frame:
                        if sof and eof:
                            # if sof appears before eof
                            if self._region_size > 1:
                                if pkt_end > pkt_start:
                                    raise MFBProtocolError(f"MFB error: a start-of-frame received without an end-of-frame! ({sof_pos=}, {eof_pos=})")

                            # end of one packet
                            self._transaction.data += self._data[r][:pkt_end].bytes

                            # read optional signals (if present) on eof
                            if self._os_vld_with == "eof":
                                for s in self._os:
                                    setattr(self._transaction, s, self._os_data[s][r].int)

                            self._recv_trans()
                            self.frame_cnt += 1
                            self.item_cnt += (len(self._transaction.data) * 8) // self._item_width

                            # start of another packet, in_frame stays True
                            self._transaction.data = self._data[r][pkt_start:].bytes

                            # read optional signals (if present) on sof
                            if self._os_vld_with == "sof":
                                for s in self._os:
                                    setattr(self._transaction, s, self._os_data[s][r].int)

                        elif sof:
                            # sof when the previous packet hasn't ended
                            raise MFBProtocolError(f"MFB error: a start-of-frame received without an end-of-frame! ({sof_pos=})")

                        elif eof:
                            # packet ends in this region and new one doesn't start
                            self._transaction.data += self._data[r][:pkt_end].bytes

                            # read optional signals (if present) on eof
                            if self._os_vld_with == "eof":
                                for s in self._os:
                                    setattr(self._transaction, s, self._os_data[s][r].int)

                            self._recv_trans()
                            in_frame = False
                            self.frame_cnt += 1
                            self.item_cnt += (len(self._transaction.data) * 8) // self._item_width

                        else:
                            # packet starts and ends in another region, in_frame stays True
                            self._transaction.data += self._data[r].bytes

                    else:
                        if sof and eof:
                            # packet starts and ends in this region, in_frame stays False
                            self._transaction.data = self._data[r][pkt_start : pkt_end].bytes

                            # read optional signals (if present) on sof or eof
                            for s in self._os:
                                setattr(self._transaction, s, self._os_data[s][r].int)

                            self._recv_trans()
                            self.frame_cnt += 1
                            self.item_cnt += (len(self._transaction.data) * 8) // self._item_width

                        elif sof:
                            # packet starts in this regions and ends in another one
                            self._transaction.data = self._data[r][pkt_start:].bytes

                            # read optional signals (if present) on sof
                            if self._os_vld_with == "sof":
                                for s in self._os:
                                    setattr(self._transaction, s, self._os_data[s][r].int)

                            in_frame = True

                        elif eof:
                            # eof when not in frame
                            raise MFBProtocolError("MFB error: an end-of-frame received before a start-of-frame!")
