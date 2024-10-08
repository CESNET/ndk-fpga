import queue
import logging

import cocotb
from cocotb.triggers import Timer

import nfb.ext.grpc
from nfb.ext.grpc import nfb_grpc_pb2_grpc
from nfb.ext.grpc import nfb_grpc_pb2


class Servicer(nfb_grpc_pb2_grpc.NfbExtensionServicer):
    def __init__(self, device, dtb, server_addr=('127.0.0.1', 63239), *args, **kwargs):
        self._log = logging.getLogger("cocotb.nfb.ext.grpc_servicer")
        self._log.setLevel(5)
        self._qrx = queue.Queue()
        self._device = device
        self._dtb = dtb
        self._server_addr = server_addr

    def start(self):
        cocotb.start_soon(self._queue_request_handle())
        self._server = nfb.ext.grpc.Server(self, *self._server_addr)

    def path(self):
        return f"libnfb-ext-grpc.so:grpc:{self._server_addr[0]}:{self._server_addr[1]}"

    @cocotb.coroutine
    def _queue_request_handle(self):
        while True:
            try:
                item = self._qrx.get(block=False)
            except queue.Empty:
                yield Timer(10, units='ns')
                continue

            node, offset, write, data, q = item
            mi_base = node.get_property('reg')[0]
            mi = self._device.mi[0] # FIXME
            fn = getattr(mi, 'write' if write else 'read')

            try:
                d = yield fn(mi_base, data)
                q.put(d)
            except Exception:
                self._log.error("comp access failed")
                q.put(None)

    def GetFdt(self, request, context):
        return nfb_grpc_pb2.FdtResponse(fdt=self._dtb)

    def ReadComp(self, request, context):
        data = self._nfb_comp_read(request.fdt_offset, request.nbyte, request.offset)
        data = [0] * request.nbyte
        return nfb_grpc_pb2.ReadCompResponse(data=bytes(data), status=0)

    def WriteComp(self, request, context):
        self._nfb_comp_write(request.fdt_offset, request.nbyte, request.offset, request.data)
        return nfb_grpc_pb2.WriteCompResponse(status=0)

    def _nfb_comp_write(self, fdtoffset, nbyte, offset, data):
        node = self._nfb._fdt.get_node(self._nfb.fdt_paths[fdtoffset])
        self._log.debug(f"comp write: size: {nbyte:>2}, offset: {offset:04x}, path: {node.path}/{node.name}, data:", data)
        q = queue.Queue()
        self._qrx.put((node, offset, True, list(data), q))
        q.get()

    def _nfb_comp_read(self, fdtoffset, nbyte, offset):
        node = self._nfb._fdt.get_node(self._nfb.fdt_paths[fdtoffset])
        q = queue.Queue()
        self._qrx.put((node, offset, False, nbyte, q))
        data = bytes(q.get())
        self._log.debug(f"comp read: size: {nbyte:>2}, offset: {offset:04x}, path: {node.path}/{node.name}, data:", data)
        return data
