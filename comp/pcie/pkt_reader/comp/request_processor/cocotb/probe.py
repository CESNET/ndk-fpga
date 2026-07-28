# probe.py: A probe specific for the PPR Request Processor output - to catch Tags that can be then reused.
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

from collections import deque
from cocotbext.ofm.mvb.transaction import MvbTrClassicSerializable, hdrfield, serializableheader
from cocotbext.ofm.base.probe import Probe, ProbeInterface
from cocotbext.ofm.mvb.monitors import MVBMonitor


# A copy from the dma_bus_pack.vhd
@serializableheader()
class DmaUphdr(MvbTrClassicSerializable):
    dma_request_length:  int = hdrfield(11)
    dma_request_type:    int = hdrfield(1)
    dma_request_firstib: int = hdrfield(2)
    dma_request_lastib:  int = hdrfield(2)
    dma_request_tag:     int = hdrfield(8)
    dma_request_unitid:  int = hdrfield(8)
    dma_request_global:  int = hdrfield(64)
    dma_request_vfid:    int = hdrfield(8)
    # pasid/pasidvld: width 0, carry no bits — OMIT
    dma_request_relaxed: int = hdrfield(1)


class PprProbeInterface(ProbeInterface):
    """Throughput probe interface for the MVB monitor."""
    interface_dict = {
        "clock"     : "clock",
        "in_reset"  : "in_reset",
        "items"     : "items",
        "item_width": "item_width",
    }

    def __init__(self, agent: MVBMonitor):
        super().__init__(agent)


class PprProbe(Probe):
    """
    A probe to catch Tags on the DMA Uphdr interface.
    """
    def __init__(self, queue: deque, interface: ProbeInterface = None, name: str | None = None, callback=None):
        super().__init__(interface, name, callback)
        self._tag_q = queue
        self._bus = self._interface._agent.bus
        self._item_mask = 2**self._interface.item_width - 1

    async def _start_probe(self) -> None:
        """
        The Tag-aqusition method.
        """
        while True:
            await self._clk_re

            if self._interface.in_reset:
                continue

            if self._interface._agent._is_valid_word(self._bus.src_rdy, self._bus.dst_rdy):
                for i in range(self._interface.items):
                    if self._bus.vld.value[i] == '1':
                        bus_val = self._bus.data.value.to_unsigned()
                        item_data = bus_val & self._item_mask
                        self._tag_q.append(DmaUphdr.deserialize(item_data).dma_request_tag)
                        bus_val >>= self._interface.item_width
