# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025-2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from cocotb.triggers import RisingEdge
from cocotbext.ofm.base.monitors import BusMonitor
from cocotbext.ofm.utils.binary import Binary, BinaryVector


class MAC_Segmented_TX_Monitor(BusMonitor):
    _signals = ["data", "valid", "inframe", "eop_empty", "error"]
    _optional_signals = ["error", "skip_crc"]

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)

    def _init_control_signals(self):
        self._bus_width = len(self.bus.data) // 8  # data width in bytes
        self._segments = len(self.bus.inframe)
        self._segment_width = self._bus_width // self._segments  # segment width in bytes

        self._data      = BinaryVector(item_count=self._segments, item_bits=self._segment_width*8, endian="little")
        self._eop_empty = BinaryVector(item_count=self._segments, item_bits=3)
        self._inframe   = Binary(bits=self._segments)
        self._error     = Binary(bits=self._segments)
        self._valid     = Binary(bits=1)

        self.frame_cnt = 0
        self.item_cnt  = 0

    def _read_control_signals(self):
        self._data.value      = self.bus.data.value.integer
        self._eop_empty.value = self.bus.eop_empty.value.integer
        self._inframe.value   = self.bus.inframe.value.integer
        self._error.value     = self.bus.error.value.integer
        self._valid.value     = self.bus.valid.value.integer

    async def _monitor_recv(self):
        clk_re = RisingEdge(self.clock)

        self._init_control_signals()

        data = b""
        in_frame = False

        while True:
            await clk_re

            if self.in_reset:
                continue

            self._read_control_signals()

            if self._valid:
                for i in range(self._segments):
                    # data on the MAC Segmented bus is sent in reverse order
                    if self._inframe[i]:
                        data += self._data[i].bytes
                        in_frame = True

                    else:
                        if in_frame:
                            data += self._data[i].bytes[: self._segment_width - self._eop_empty[i].int]
                            self._recv(data)
                            data = b""
                            in_frame = False
                            self.frame_cnt += 1
