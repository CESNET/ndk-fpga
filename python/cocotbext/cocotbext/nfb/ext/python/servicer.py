import logging
import cocotb

import nfb.ext.python as ext


class Servicer(ext.AbstractNfb):
    class NdpQueue(ext.AbstractNdpQueue):
        _burst_temp = []

        def __init__(self, q):
            self._q = q

        def start(self):
            pass

        def stop(self):
            pass

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
        def burst_get(self, pkts):
            p = [(bytes(pkts[i][0]), bytes(pkts[i][1]), pkts[i][2]) for i in range(len(pkts))]
            self._burst_temp += p
            return p

        @cocotb.function
        def burst_put(self):
            for pkt in self._burst_temp:
                yield self._q.sendmsg(pkt)
            self._burst_temp.clear()

    def __init__(self, device, dtb, *args, **kwargs):
        self._log = logging.getLogger("cocotb.nfb.ext.python_servicer")
        self._device = device
        super().__init__(dtb)

    def queue_open(self, index, dir, flags):
        ndp = self._device.dma
        base, attr = (Servicer.NdpQueueRx, ndp.rx) if dir == 0 else (Servicer.NdpQueueTx, ndp.tx)
        return base(attr[index])

    def get_node_base(self, bus_node, node):
        # TODO: fix mi[0]
        return (self._device.mi[0], node.get_property("reg")[0])

    @cocotb.function
    def read(self, bus_node, node, offset, nbyte):
        mi, base = self.get_node_base(bus_node, node)
        data = yield mi.read(offset, nbyte)
        if data is None:
            data = bytes()
        self._log.debug(f"MI read : size: {nbyte:>2}, offset: {offset:04x}, path: {node.path}/{node.name}, data: {data.hex()}")
        return data

    @cocotb.function
    def write(self, bus_node, node, offset, data):
        mi, base = self.get_node_base(bus_node, node)
        nbyte = len(data)
        self._log.debug(f"MI write: size: {nbyte:>2}, offset: {offset:04x}, path: {node.path}/{node.name}, data: {data.hex()}")
        yield mi.write(offset, data)
