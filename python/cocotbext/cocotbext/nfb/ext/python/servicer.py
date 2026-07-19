# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2023-2026 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>

import re
import logging
import cocotb

import nfb.ext.python as ext


class Servicer(ext.AbstractNfb):
    class NdpQueue(ext.AbstractNdpQueue):
        def __init__(self, q):
            self._burst_temp = []
            self._q = q

        @cocotb.task.resume
        async def start(self):
            await self._q.start()

        @cocotb.task.resume
        async def stop(self):
            await self._q.stop()

    class NdpQueueRx(NdpQueue, ext.AbstractNdpQueueRx):
        def burst_get(self, count):
            msg = self._q.recvmsg()
            if msg is None:
                return []

            self._burst_temp.append(msg)
            return [msg]

        def burst_put(self):
            self._burst_temp.clear()

    class NdpQueueTx(NdpQueue, ext.AbstractNdpQueueTx):
        @cocotb.task.resume
        async def burst_get(self, pkts):
            p = [(bytes(pkts[i][0]), bytes(pkts[i][1]), pkts[i][2]) for i in range(len(pkts))]
            n = await self._q.wait_sendable(p)
            if n != len(p):
                return []

            self._burst_temp.extend(p)
            return p

        @cocotb.task.resume
        async def burst_put(self):
            last_index = len(self._burst_temp) - 1
            for i, pkt in enumerate(self._burst_temp):
                await self._q.sendmsg(pkt, i == last_index)
            self._burst_temp.clear()

    def __init__(self, device, dtb, *args, **kwargs):
        self._log = logging.getLogger(__name__)
        self._device = device
        super().__init__(dtb)

    def queue_open(self, index, dir, flags):
        ndp = self._device.dma
        base, attr = (Servicer.NdpQueueRx, ndp.rx) if dir == 0 else (Servicer.NdpQueueTx, ndp.tx)
        return base(attr[index])

    def get_node_base(self, bus_node, node):
        m = re.search(r'PCI(?P<pci>\d+),BAR(?P<bar>\d+)', bus_node.get_property("resource").value)
        pci, _ = int(m.group('pci')), int(m.group('bar'))
        mi = self._device.mi[pci]
        return (mi, node.get_property("reg")[0])

    @cocotb.task.resume
    async def read(self, bus_node, node, offset, nbyte):
        mi, base = self.get_node_base(bus_node, node)
        data = await mi.read(offset, nbyte)
        if data is None:
            data = bytes()
        self._log.debug(f"MI read : size: {nbyte:>2}, offset: {offset:04x}, path: {node.path}/{node.name}, data: {data.hex()}")
        return data

    @cocotb.task.resume
    async def write(self, bus_node, node, offset, data):
        mi, base = self.get_node_base(bus_node, node)
        nbyte = len(data)
        self._log.debug(f"MI write: size: {nbyte:>2}, offset: {offset:04x}, path: {node.path}/{node.name}, data: {data.hex()}")
        await mi.write(offset, data)
