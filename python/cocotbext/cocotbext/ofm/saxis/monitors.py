# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 DynaNIC Semiconductors ltd.
# Author(s): Vlastimil Kosar <kosar@dyna-nic.com>

from cocotb_bus.monitors import BusMonitor
from cocotb.triggers import ReadOnly, RisingEdge


class SAXISMonitor(BusMonitor):
    """Monitor of the Segmented AXI-Stream of the AMD DCMAC (PG369), 128-bit segments.

    Received frames are passed to the callbacks as ``bytes``. The ERR flag of
    the last segment of every frame is stored in ``frame_err`` in the order of
    the frames. READY is optional, the RX interface of the DCMAC has none.
    A frame in progress is dropped when the reset is active.
    """

    _signals = ["data", "ena", "sop", "eop", "err", "mty", "valid"]
    _optional_signals = ["ready"]

    def __init__(self, *args, **kwargs):
        BusMonitor.__init__(self, *args, **kwargs)

        self._segments = len(self.bus.sop)
        self.frame_cnt = 0
        self.frame_err: list[bool] = []

    async def _monitor_recv(self):
        clk_redge = RisingEdge(self.clock)
        read_only = ReadOnly()
        ready = getattr(self.bus, "ready", None)

        packet = None
        while True:
            # Sampled after all writes of this time step, see SAXISProtocolChecker._run.
            await clk_redge
            await read_only

            if self.in_reset:
                packet = None
                continue

            if not (self.bus.valid.value == 1 and (ready is None or ready.value == 1)):
                continue

            ena = self.bus.ena.value.to_unsigned()
            sop = self.bus.sop.value.to_unsigned()
            eop = self.bus.eop.value.to_unsigned()
            err = self.bus.err.value.to_unsigned()

            for i in range(self._segments):
                if not ena & (1 << i):
                    continue

                if sop & (1 << i):
                    assert packet is None, "SAXIS: SOP received inside a frame"
                    packet = bytearray()
                assert packet is not None, "SAXIS: data received outside a frame"

                data = self.bus.data[i].value.to_bytes(byteorder="little")
                if eop & (1 << i):
                    data = data[:len(data) - self.bus.mty[i].value.to_unsigned()]

                packet += data

                if eop & (1 << i):
                    self.frame_cnt += 1
                    self.frame_err.append(bool(err & (1 << i)))
                    self._recv(bytes(packet))
                    packet = None
