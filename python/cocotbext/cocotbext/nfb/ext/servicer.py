import queue
import logging

import cocotb
from cocotb.triggers import Timer


class CommonAsyncServicer():
    def path(self):
        raise NotImplementedError()

    def get_node_base(self, bus_node, comp_node):
        # TODO: fix mi[0]
        return (self._device.mi[0], comp_node.get_property("reg")[0])

    def start(self):
        pass

    @cocotb.function
    def read(self, bus_node, comp_node, offset, nbyte):
        try:
            mi, base = self.get_node_base(bus_node, comp_node)
            data = yield mi.read(base + offset, nbyte)
            self._log.debug(f"comp read: size: {nbyte:>2}, offset: {offset:04x}, path: {comp_node.path}/{comp_node.name}, data:", data)
        except Exception as e:
            self._log.error("comp read failed: ", e)
        return bytes(data)

    @cocotb.function
    def write(self, bus_node, comp_node, offset, data):
        try:
            mi, base = self.get_node_base(bus_node, comp_node)
            nbyte = len(data)
            data = list(data)
            self._log.debug(f"comp write: size: {nbyte:>2}, offset: {offset:04x}, path: {comp_node.path}/{comp_node.name}, data:", data)
            yield mi.write(base + offset, data)
        except Exception as e:
            self._log.error("comp write failed:", e)
        return len(data)


class CommonServicer(CommonAsyncServicer):
    def __init__(self, device, dtb, server_addr=('127.0.0.1', 63239), *args, **kwargs):
        self._log = logging.getLogger("cocotb.nfb.ext.servicer")
        #self._log.setLevel(5)
        self._qrx = queue.Queue()
        self._device = device
        self._dtb = dtb

    def start(self):
        cocotb.start_soon(self._queue_request_handle())

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
