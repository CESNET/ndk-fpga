# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2024-2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

import logging

import cocotb
import nfb.ext.python as ext


class Servicer(ext.AbstractNfb):
    def __init__(self, device, dtb, *args, **kwargs):
        self._log = logging.getLogger(__name__)
        self._device = device
        super().__init__(dtb)

    def get_node_base(self, bus_node, node):
        # TODO: fix mi[0]
        return (self._device, node.get_property("reg")[0])

    @cocotb.task.resume
    async def read(self, bus_node, node, offset, nbyte):
        mi, base = self.get_node_base(bus_node, node)
        data = await mi.read(offset, nbyte)
        self._log.debug(f"comp read: size: {nbyte:>2}, offset: {offset:04x}, path: {node.path}/{node.name}, data:", data)
        return bytes(data)

    @cocotb.task.resume
    async def write(self, bus_node, node, offset, data):
        mi, base = self.get_node_base(bus_node, node)
        nbyte = len(data)
        #data = list(data)
        self._log.debug(f"comp write: size: {nbyte:>2}, offset: {offset:04x}, path: {node.path}/{node.name}, data:", data)
        await mi.write(offset, data)
