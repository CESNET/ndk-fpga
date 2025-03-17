# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>

import re
import logging
import queue
import cocotb

from cocotb.triggers import Timer

from threading import Event

import nfb.ext.protobuf.v1.nfb_pb2 as nfb_pb
import nfb.ext.protobuf.v1.nfb_pb2_grpc as nfb_pb_grpc


class CompRequest():
    def __init__(self, rd, path, offset, nbyte, data=None):
        self.rd = rd
        self.path = path
        self.offset = offset
        self.nbyte = nbyte
        self.data = data
        self.event = Event()

    def set(self, data):
        self.data = data
        self.event.set()

    def wait(self):
        self.event.wait()
        return self.data


class NfbServicer(nfb_pb_grpc.NfbServicer):
    def __init__(self, dev):
        self._log = logging.getLogger(__name__)
        self._dev = dev
        self._events = queue.Queue()
        self._requests = queue.Queue(10)

        cocotb.start_soon(self._mi_req_thread())

    async def _mi_req_thread(self):
        timer = Timer(10, units='ns')

        while True:
            while self._requests.empty():
                await timer

            req = self._requests.get(False)

            mi, base = self._comp_addr(req.path)
            addr = req.offset + base
            req_type = "Read" if req.rd else "Write"
            self._log.debug(f"{req_type:<5}: size: {req.nbyte:>4}, offset: {hex(req.offset):>8}, base: {hex(base):>10} {req.path}")

            if req.rd:
                data = await mi.read(addr, req.nbyte)
            else:
                data = await mi.write(addr, req.data)

            req.set(data)

    def _comp_addr(self, path):
        node = self._dev.nfb.fdt.get_node(path)
        base = node.get_property("reg")[0]

        p = node.parent
        while p:
            compatible = p.get_property("compatible")
            if compatible and compatible.value == "netcope,bus,mi":
                m = re.search(r'PCI(?P<pci>\d+),BAR(?P<bar>\d+)', p.get_property("resource").value)
                pci, _ = int(m.group('pci')), int(m.group('bar'))
                mi = self._dev.mi[pci]
                break
            p = p.parent

        return mi, base

    def resp_force(self):
        while not self._events.empty():
            self._events.get(False).set()

    def GetFdt(self, req, context):
        return nfb_pb.FdtResponse(fdt=bytes(self._dev.nfb.fdt.to_dtb()))

    def ReadComp(self, req, context):
        req = CompRequest(True, req.path, req.offset, req.nbyte)
        self._requests.put(req)
        self._events.put(req.event)
        data = req.wait()
        self._events.get(False)
        return nfb_pb.ReadCompResponse(status=0, data=data)

    def WriteComp(self, req, context):
        req = CompRequest(False, req.path, req.offset, req.nbyte, req.data)
        self._requests.put(req)
        #_ = req.wait()
        return nfb_pb.WriteCompResponse(status=0)
