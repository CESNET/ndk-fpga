# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from cocotb_bus.monitors import BusMonitor
from cocotb.triggers import RisingEdge
from cocotbext.ofm.utils.binary import Binary, BinaryVector, BinarySignals


class MAC_Segmented_TX_Monitor(BusMonitor):
    _signals = ["data", "valid", "inframe", "eop_empty", "error"]
    _optional_signals = ["error", "skip_crc"]

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    def _init_control_signals(self):
        self._bus_width = len(self.bus.data) // 8  # data width in bytes
        self._segments = len(self.bus.inframe)
        self._segment_width = self._bus_width // self._segments  # segment width in bytes

        self._signal = BinarySignals(parent=self, params={
            "data"      : BinaryVector(item_count=self._segments, item_bits=self._segment_width*8, endian="little"),
            "eop_empty" : BinaryVector(item_count=self._segments, item_bits=3),
            "inframe"   : Binary(bits=self._segments),
            "error"     : Binary(bits=self._segments),
            "valid"     : Binary(bits=1)
        })

        self.frame_cnt = 0
        self.item_cnt  = 0

    async def _monitor_recv(self):
        clk_re = RisingEdge(self.clock)

        self._init_control_signals()

        data = b""
        in_frame = False

        while True:
            await clk_re

            if self.in_reset:
                continue

            if self._signal.valid:
                for i in range(self._segments):
                    # data on the MAC Segmented bus is sent in reverse order
                    if self._signal.inframe.reversed()[i]:
                        data += self._signal.data[i].bytes
                        in_frame = True

                    else:
                        if in_frame:
                            data += self._signal.data[i].bytes[: self._segment_width - self._signal.eop_empty.vreversed()[i].int]
                            self._recv(data)
                            data = b""
                            in_frame = False
                            self.frame_cnt += 1
