# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2023-2026 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>

import cocotb
from cocotb.triggers import Timer

import nfb.libnetcope
import nfb.libnfb

e = cocotb.task.bridge

NDP_RX_CALYPTE_BLOCK_SIZE = 128
NDP_TX_CALYPTE_BLOCK_SIZE = 32


class QueueManager:
    def __init__(self, dev):
        nfb = dev.nfb
        compatibles = ([
            (QueueNdpRx, "netcope,dma_ctrl_ndp_rx", 0),
            (QueueNdpRxCalypte, "cesnet,dma_ctrl_calypte_rx", 0),
        ], [
            (QueueNdpTx, "netcope,dma_ctrl_ndp_tx", 1),
            (QueueNdpTxCalypte, "cesnet,dma_ctrl_calypte_tx", 1),
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
        self._wait_timer = Timer(10, unit="ns")
        self._ctrl = nfb.libnetcope.DmaCtrlNdp(dev.nfb, node)
        self._ram = dev.ram
        self._state = 0
        self._dsc_free = 0

        bs = self._buffer_size = 1048576
        self._packet_length_max = 4096
        buf_spacing = self._buffer_size * 2

        self._packet_count_max = self._buffer_size // self._packet_length_max

        self._desc_cnt = self._packet_count_max

        bb = self._buffer_base = buf_index * buf_spacing
        self._dsc_base = bb + bs + (bs // 4) * 0
        self._hdr_base = bb + bs + (bs // 4) * 1 # if self._dir == 0 else 0
        self._upd_base = bb + bs + (bs // 4) * 2

    def update_desc_upper_address(self, buffer_addr):
        desc = self._ctrl.desc0(buffer_addr)
        if self._ctrl.last_upper_addr == desc:
            return False

        self._ctrl.last_upper_addr = desc
        self._push_one_desc(desc)
        return True

    def _push_one_desc(self, desc):
        assert self._state != 0, "Queue not started yet"

        self._ram.wint(self._dsc_base + self._ctrl.sdp * 8, desc, 8)
        self._ctrl.sdp += 1
        self._dsc_free -= 1

    async def stop(self):
        await e(self._ctrl.stop)()

    async def start(self):
        if self._upd_base + 4 > len(self._ram._mem):
            raise Exception("Not enough memory for QueueNdp in RAM object. "
                            "Try to increase RAM size or decrease number of queues")

        upd = memoryview(self._ram._mem)[self._upd_base:self._upd_base + 8]
        try:
            await e(self._ctrl.start)(self._dsc_base, self._hdr_base, self._upd_base, upd, self._desc_cnt, self._desc_cnt)
        except Exception:
            await e(self._ctrl.stop)(force=True)
            await e(self._ctrl.start)(self._dsc_base, self._hdr_base, self._upd_base, upd, self._desc_cnt, self._desc_cnt)

        self._dsc_free = self._ctrl.mdp

        self._npi = 0
        self._state = 1
        self._post_start()

    def _post_start(self):
        pass

    async def read_stats(self):
        return await e(self._ctrl.read_stats)()


class QueueNdpRx(QueueNdp):
    def __init__(self, nfb, node, buf_index):
        self._dir = 0
        QueueNdp.__init__(self, nfb, node, buf_index)

    async def _push_desc(self, flush=True):
        assert self._state != 0, "Queue not started yet"

        while self._dsc_free < 2:
            # TODO: check if can be flushed
            await self._wait_timer

        buffer_addr = self._buffer_base + self._ctrl.sdp * self._packet_length_max
        self.update_desc_upper_address(buffer_addr)

        #desc2 = (2 << 62) | ((self._packet_length_max & 0xFFFF) << 32) | (buffer_addr & 0x3FFFFFFF)
        desc = self._ctrl.desc2(buffer_addr, self._packet_length_max, next=False)
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

        buffer_addr = self._buffer_base + self._ctrl.shp * self._packet_length_max
        self._ctrl.shp += 1
        self._dsc_free += 1  # FIXME: classical computation?
        return (bytes(self._ram.r(buffer_addr, length)), bytes(), 0)


class QueueNdpRxCalypte(QueueNdpRx):
    def __init__(self, nfb, node, buf_index):
        QueueNdpRx.__init__(self, nfb, node, buf_index)
        # Expected polarity of the next not-yet-consumed header's "valid" bit; flips
        # every time the header ring wraps (see recvmsg() below).
        self._valid_flag = 1
        self._rx_sdp_flush_pending = False

    def _post_start(self):
        self._rx_sdp_flush_pending = False
        cocotb.start_soon(self._sdp_flush_loop())

    async def _sdp_flush_loop(self):
        # recvmsg() runs synchronously (invoked straight from the C ndp_rx_burst_get
        # trampoline), so it can only update self._ctrl.sdp locally - it cannot await
        # the MI write that actually informs hardware which data-buffer blocks have
        # been freed. Without this write-back, hardware's own free-space bookkeeping
        # never advances past whatever it was given at start, so every packet after
        # the first one that exhausts it is silently discarded. This loop is the
        # asynchronous counterpart, mirroring what the real driver's
        # _ndp_queue_rx_sync_v3_us() does on real hardware.
        while True:
            await self._wait_timer
            if self._rx_sdp_flush_pending:
                self._rx_sdp_flush_pending = False
                await e(self._ctrl.flush_sp)()

    def recvmsg(self, cnt=-1, timeout=0):
        hdr_off = self._hdr_base + 8 * self._ctrl.shp
        word = bytes(self._ram.r(hdr_off, 8))

        valid, frame_len, frame_ptr, metadata = self._ctrl.calypte_hdr_decode(word)
        if valid != bool(self._valid_flag):
            return None

        header_size = metadata & 0xFF
        length = frame_len - header_size

        buffer_addr = self._dsc_base + frame_ptr * NDP_RX_CALYPTE_BLOCK_SIZE

        self._ctrl.shp += 1
        self._dsc_free += 1
        if self._ctrl.shp == 0:
            self._valid_flag ^= 1

        blocks = (frame_len + NDP_RX_CALYPTE_BLOCK_SIZE - 1) // NDP_RX_CALYPTE_BLOCK_SIZE
        self._ctrl.sdp += blocks
        self._rx_sdp_flush_pending = True

        if header_size:
            hdr_bytes = bytes(self._ram.r(buffer_addr, header_size))
            return (bytes(self._ram.r(buffer_addr + header_size, length)), hdr_bytes, 0)
        return (bytes(self._ram.r(buffer_addr, length)), bytes(), 0)


class QueueNdpTx(QueueNdp):
    def __init__(self, nfb, node, buf_index):
        self._dir = 1
        QueueNdp.__init__(self, nfb, node, buf_index)

    def _get_free_descs(self, sdp):
        hdp = self._ctrl.update_hdp()
        return (hdp - sdp - 1) & self._ctrl.mhp

    async def write(self, pkt):
        pass

    async def send(self, pkt, flush=True):
        return await self.sendmsg((pkt, [], flush))

    async def wait_sendable(self, msgs):
        ret = min(max(0, self._get_free_descs(self._ctrl.sdp) - 2), len(msgs))
        if ret != len(msgs):
            # The pynfb sendmsg function (API) doesn't returns until all messages are sent
            # If there is no space in NDP buffer, wait some time to let the HDP to update
            await self._wait_timer
        return ret

    async def sendmsg(self, pkt, flush=True):
        pkt, hdr, flags = pkt
        pkt_hdr = pkt + hdr
        assert self._ctrl.mtu[0] <= len(pkt_hdr) <= min(self._packet_length_max, self._ctrl.mtu[1])
        assert self._state != 0, "Queue not started yet"

        while self._get_free_descs(self._ctrl.sdp) < 2:
            await self._wait_timer

        buffer_addr = self._buffer_base + self._npi * self._packet_length_max
        self.update_desc_upper_address(buffer_addr)

        self._ram.w(buffer_addr, pkt + hdr)
        desc = self._ctrl.desc2(buffer_addr, len(pkt + hdr), meta=0, next=False, hdr_length=len(hdr))
        self._push_one_desc(desc)
        self._npi = (self._npi + 1) % self._packet_count_max

        if flush:
            await self.flush()

    async def flush(self):
        if self._state == 1:
            await e(self._ctrl.flush_sdp)()
            self._sdp_hw = self._ctrl.sdp


class QueueNdpTxCalypte(QueueNdpTx):
    def __init__(self, nfb, node, buf_index):
        QueueNdpTx.__init__(self, nfb, node, buf_index)

        dev_nfb = nfb.nfb
        self._data_buff = dev_nfb.comp_open(dev_nfb.fdt_get_phandle(node.get_property('data_buff').value))
        self._hdr_buff = dev_nfb.comp_open(dev_nfb.fdt_get_phandle(node.get_property('hdr_buff').value))
        self._tx_sdp = 0
        self._tx_shp = 0
        self._tx_hdp_shadow = 0
        self._tx_free_bytes = 0

    def _post_start(self):
        self._tx_hdp_shadow = 0
        self._tx_free_bytes = self._ctrl.mdp + 1 - NDP_TX_CALYPTE_BLOCK_SIZE

    def _tx_frame_space(self, frame_len):
        return (frame_len + NDP_TX_CALYPTE_BLOCK_SIZE - 1) & ~(NDP_TX_CALYPTE_BLOCK_SIZE - 1)

    async def _tx_refresh_free_bytes(self):
        hdp = await e(self._ctrl.read_hdp)()
        self._tx_free_bytes += (hdp - self._tx_hdp_shadow) & self._ctrl.mdp
        self._tx_hdp_shadow = hdp

    async def wait_sendable(self, msgs):
        await self._tx_refresh_free_bytes()

        free = self._tx_free_bytes
        ret = 0
        for pkt, hdr, flags in msgs:
            frame_space = self._tx_frame_space(len(pkt) + len(hdr))
            if frame_space > free:
                break
            free -= frame_space
            ret += 1

        if ret != len(msgs):
            await self._wait_timer
        return ret

    async def sendmsg(self, pkt, flush=True):
        pkt, hdr, flags = pkt
        assert self._state != 0, "Queue not started yet"

        header_size = len(hdr)
        frame_len = len(pkt) + header_size
        assert self._ctrl.mtu[0] <= frame_len <= min(self._packet_length_max, self._ctrl.mtu[1])

        frame_space = self._tx_frame_space(frame_len)
        while self._tx_free_bytes < frame_space:
            await self._tx_refresh_free_bytes()
            if self._tx_free_bytes < frame_space:
                await self._wait_timer

        frame_ptr = self._tx_sdp
        await e(self._data_buff.write)(frame_ptr, hdr + pkt)
        word = frame_len | (frame_ptr << 16) | (header_size << 40) | ((flags & 0xF) << 48)
        await e(self._hdr_buff.write)(self._tx_shp * 8, word.to_bytes(8, byteorder='little'))

        self._tx_free_bytes -= frame_space
        self._tx_sdp = (self._tx_sdp + frame_space) & self._ctrl.mdp
        self._tx_shp = (self._tx_shp + 1) & self._ctrl.mhp

    async def flush(self):
        # Writing the header in sendmsg() is itself what makes the transmission visible to hardware
        pass
