import cocotb
from cocotb.triggers import Timer

import nfb.libnetcope
import nfb.libnfb

e = cocotb.external


class QueueManager:
    def __init__(self, dev):
        nfb = dev.nfb
        compatibles = ([
            (QueueNdpRx, "netcope,dma_ctrl_ndp_rx", 0),
        ], [
            (QueueNdpTx, "netcope,dma_ctrl_ndp_tx", 1),
        ])

        self.rx, self.tx = (
            [
                queue(dev, node, i * 2 + buf_off)
                for queue, compatible, buf_off in d
                for i, node in enumerate(nfb.fdt_get_compatible(compatible))
            ] for d in compatibles
        )

    async def send(self, pkt, index=None, flush=True):
        if index is None:
            index = [i for i in range(len(self.tx))]
        for i in index:
            await self.tx[i].send(pkt, flush)

    async def flush(self, index=None):
        if index is None:
            index = [i for i in range(len(self.tx))]
        for i in index:
            await self.tx[i].flush()


class QueueNdp:
    def __init__(self, dev, node, buf_index):
        self._ctrl = nfb.libnetcope.DmaCtrlNdp(dev.nfb, node)
        self._ram = dev.ram
        self._state = 0

        bs = self._buffer_size = 1048576
        self._packet_length_max = 4096
        buf_spacing = self._buffer_size * 2

        self._packet_count_max = self._buffer_size // self._packet_length_max

        self._desc_cnt = self._packet_count_max

        bb = self._buffer_base = buf_index * buf_spacing
        self._dsc_base = bb + bs + (bs // 4) * 0
        self._hdr_base = bb + bs + (bs // 4) * 1 # if self._dir == 0 else 0
        self._upd_base = bb + bs + (bs // 4) * 2

    def update_desc_upper_address(self, ba):
        desc = self._ctrl.desc0(ba)
        if self._ctrl.last_upper_addr == desc:
            return False
        self._push_one_desc(desc)
        return True

    def _push_one_desc(self, desc):
        self._ram.wint(self._dsc_base + self._ctrl.sdp * 8, desc, 8)
        self._ctrl.sdp += 1
        self._dsc_free -= 1

    async def start(self):
        upd = memoryview(self._ram._mem)[self._upd_base:self._upd_base + 8]
        try:
            await e(self._ctrl.start)(self._dsc_base, self._hdr_base, self._upd_base, upd, self._desc_cnt, self._desc_cnt)
        except Exception:
            await e(self._ctrl.stop)(force=True)
            await e(self._ctrl.start)(self._dsc_base, self._hdr_base, self._upd_base, upd, self._desc_cnt, self._desc_cnt)

        self._dsc_free = self._ctrl.mdp

        self._npi = 0
        self._state = 1

    async def read_stats(self):
        return await e(self._ctrl.read_stats)()


class QueueNdpRx(QueueNdp):
    def __init__(self, nfb, node, buf_index):
        self._dir = 0
        QueueNdp.__init__(self, nfb, node, buf_index)

    async def _push_desc(self, flush=True):
        if self._state == 0:
            await self.start()

        while self._dsc_free < 2:
            # TODO: check if can be flushed
            await Timer(10, units="ns")

        ba = self._buffer_base + self._ctrl.sdp * self._packet_length_max
        self.update_desc_upper_address(ba)

        #desc2 = (2 << 62) | ((self._packet_length_max & 0xFFFF) << 32) | (ba & 0x3FFFFFFF)
        desc = self._ctrl.desc2(ba, self._packet_length_max, next=False)
        self._push_one_desc(desc)
        if flush:
            await e(self._ctrl.flush_sp)()

    #async def read(self):
    #    return []

    def recv(self, cnt=-1, timeout=0):
        return [x[0] for x in self.readmsg()]

    def recvmsg(self, cnt=-1, timeout=0):
        if self._ctrl.shp == self._ctrl.update_hhp():
            return None

        hdr = self._ram.rint(self._hdr_base + 4 * self._ctrl.shp, 4)
        length = hdr & 0xFFFF

        ba = self._buffer_base + self._ctrl.shp * self._packet_length_max
        self._ctrl.shp += 1
        return (bytes(self._ram.r(ba, length)), bytes(), 0)


class QueueNdpTx(QueueNdp):
    def __init__(self, nfb, node, buf_index):
        self._dir = 1
        QueueNdp.__init__(self, nfb, node, buf_index)

    async def write(self, pkt):
        pass

    async def send(self, pkt, flush=True):
        return self.sendmsg((pkt, [], flush))

    async def sendmsg(self, pkt, flush=True):
        pkt, hdr, flags = pkt
        pkt_hdr = pkt + hdr
        assert self._ctrl.mtu[0] <= len(pkt_hdr) <= min(self._packet_length_max, self._ctrl.mtu[1])

        # INFO: may be obsolete, the libnfb.ndp starts it
        if self._state == 0:
            await self.start()

        while self._dsc_free < 2:
            hdp = self._ctrl.update_hdp()
            #prev = self._dsc_free
            self._dsc_free = (hdp - (self._ctrl.sdp + 1)) & self._ctrl.mdp
            if self._dsc_free < 2:
                # FIXME: when flush = False, assure that sdp is flushed when
                #if ((self._sdp_hw - (self._ctrl.sdp + 1))) & self._ctrl.mdp) < 2:
                #    self.flush()
                await Timer(5, units="us")

        ba = self._buffer_base + self._npi * self._packet_length_max
        self.update_desc_upper_address(ba)

        self._ram.w(ba, pkt + hdr)
        desc = self._ctrl.desc2(ba, len(pkt + hdr), meta=0, next=False, hdr_length=len(hdr))
        self._push_one_desc(desc)
        self._npi = (self._npi + 1) % self._packet_count_max

        if flush:
            await self.flush()

    async def flush(self):
        if self._state == 1:
            await e(self._ctrl.flush_sdp)()
            self._sdp_hw = self._ctrl.sdp
