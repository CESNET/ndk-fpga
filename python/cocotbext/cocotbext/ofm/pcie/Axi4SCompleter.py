# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>

import cocotb
import cocotb.queue
from cocotb.triggers import Event, RisingEdge

from ..utils import concat, SerializableHeader
from .PcieHeaders import CQHeader, CCHeader, CQUser


class CQHeaderEmpty(SerializableHeader):
    items = list(zip([], []))


class Axi4SCompleter:
    def __init__(self, cq_driver, cc_driver, cc_monitor):
        self._cq = cq_driver
        self._cc = cc_driver
        self._ccm = cc_monitor
        self._queue_send = cocotb.queue.Queue()
        self._queue_recv = cocotb.queue.Queue()
        self._axi_width = len(self._cq.bus.TDATA) // 8

        self._cc_inframe = None
        self._completions = {}
        self._read_requests = {}
        self._tag_queue = cocotb.queue.PriorityQueue()
        [self._tag_queue.put_nowait(i) for i in range(2**5)]

        cc_monitor.add_callback(self._handle_cc_transaction)
        cocotb.start_soon(self._cq_loop())

    async def _cq_loop(self):
        re = RisingEdge(self._cq.clock)
        await re

        while True:
            if self._queue_send.empty():
                await re
                continue

            item, trigger = self._queue_send.get_nowait()
            tag = None
            if item[2] == 0:  # req_type = read
                tag = await self._tag_queue.get()
                self._read_requests[tag] = (trigger, item, [])
            if tag is None:
                trigger.set()

            await self._cq_req(*item, tag=tag, sync=False)

    def _handle_cc_transaction(self, tr):
        data = list(reversed(tr["TDATA"]))
        # FIXME: Monitor sends values as bytes
        tlast = bool(tr['TLAST'][0])

        # INFO: tkeep not checked for continuity
        tkeep = int.from_bytes(tr['TKEEP'], byteorder='big')
        vld_bytes = int(tkeep).bit_count() * 4

        if self._cc_inframe is None:
            h = len(CCHeader()) // 8
            hdrbytes, data = data[:h], data[h:]
            vld_bytes -= h
            self._cc_inframe = CCHeader.deserialize(int.from_bytes(hdrbytes, byteorder='little'))

        data = data[:int(vld_bytes)]
        hdr = self._cc_inframe

        trigger, item, req_data = self._read_requests[hdr.tag]
        addr, byte_count, req_type, orig_data = item

        # Splitted completion for request
        is_first = len(req_data) == 0
        offset = addr % 4 if is_first else 0
        data = data[offset:]

        rem = byte_count - len(req_data)
        is_last = len(data) >= rem
        data = data[:rem] if is_last else data[:]
        req_data.extend(data)

        if tlast:
            self._cc_inframe = None
            if is_last:
                del self._read_requests[hdr.tag]
                trigger.set(req_data)
                self._tag_queue.put_nowait(hdr.tag)

    async def _cq_req(self, addr, byte_count, req_type=0, data=[], tag=None, sync=True):
        header_empty = CQHeaderEmpty()
        header = CQHeader()
        user = CQUser()

        user.firstBe0 = [0xF, 0xE, 0xC, 0x8][addr % 4]
        user.lastBe0 = [0xF, 0x1, 0x3, 0x7][(addr + byte_count) % 4]
        user.sop0 = 1

        dwords = (addr % 4 + byte_count + 3) // 4
        if dwords <= 1:
            user.firstBe0 &= user.lastBe0
            user.lastBe0 = 0

        if req_type == 1:
            assert len(data) == byte_count
            data = [0] * (addr % 4) + data + [0] * (-(addr + byte_count) % 4)

        if tag is not None:
            header.tag = tag
        header.bar_apper = 26
        header.addr = addr >> 2
        header.dword_count = dwords
        header.req_type = req_type

        while len(data) or len(header):
            cnt = min(self._axi_width - len(header) // 8, len(data))
            tdata = concat([(header.serialize(), len(header))] + list(zip(data[:cnt], [8] * cnt)))
            tuser = user.serialize()
            tkeep = 2**(cnt // 4 + len(header) // 32) - 1
            await self._cq.write({"TDATA": tdata, "TUSER": tuser, "TKEEP": tkeep}, sync=sync)

            header = header_empty
            user.sop0 = 0
            data = data[cnt:]

    async def read(self, addr: int, byte_count: int) -> bytes:
        # TODO: split big reads to more transactions
        e = Event()
        await self._queue_send.put(((addr, byte_count, 0, []), e))
        await e.wait()
        return bytes(e.data)

    async def write(self, addr: int, data: bytes):
        # TODO: split big writes to more transactions
        e = Event()
        data = list(data)
        await self._queue_send.put(((addr, len(data), 1, data), e))
        data = await e.wait()

    async def read64(self, addr):
        rawdata = await self.read(addr, 8)
        return int.from_bytes(bytes(rawdata), byteorder="little")

    async def read32(self, addr):
        rawdata = await self.read(addr, 4)
        return int.from_bytes(bytes(rawdata), byteorder="little")

    async def write32(self, addr, val):
        await self.write(addr, list(val.to_bytes(4, byteorder="little")))

    async def write64(self, addr, val):
        await self.write(addr, list(val.to_bytes(8, byteorder="little")))
