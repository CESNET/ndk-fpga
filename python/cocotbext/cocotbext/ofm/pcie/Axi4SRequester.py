# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>

import logging
import cocotb
from cocotb.queue import Queue
from ..utils import concat, numberOfSetBits, bitmask, byte_serialize, byte_deserialize
from .PcieHeaders import RQHeader, RCHeader, RQUser, RCUser, fbe2offset


class Frame(object):
    def __init__(self, meta):
        self.meta = meta
        self.data = 0
        self.dwords = 0

    def append(self, data, dwords):
        self.data |= (data & bitmask(dwords * 32)) << (self.dwords * 32)
        self.dwords += dwords
        return self


class Axi4SRequester:
    def __init__(self, ram, rq_driver, rc_driver, rq_monitor):
        self._ram = ram
        self._rq = rq_driver
        self._rc = rc_driver
        self._rcm = rq_monitor

        self._q = Queue()
        self._rq_inframe = False
        self._rq_pending = 0
        self._rq_pending_dwords = 0
        self._rq_pending_meta = ()

        self._rq_width = len(self._rq.bus.TDATA)

        self._log = logging.getLogger(__name__)

        rq_monitor.add_callback(self.handle_rq_transaction)

        cocotb.start_soon(self.handle_response())

    def handle_rq_transaction(self, transaction):
        tuser = RQUser.deserialize(int.from_bytes(transaction['TUSER'], byteorder='big'))
        tdata = int.from_bytes(transaction['TDATA'], byteorder='big')

        sop_pos = [getattr(tuser, 'sop{:d}'.format(i)) for i in range(bin(tuser.sop).count("1"))]
        eop_pos = [getattr(tuser, 'eop{:d}'.format(i)) for i in range(bin(tuser.eop).count("1"))]
        fbe = [getattr(tuser, 'first_be{:d}'.format(i)) for i in range(bin(tuser.sop).count("1"))]
        lbe = [getattr(tuser, 'last_be{:d}'.format(i)) for i in range(bin(tuser.sop).count("1"))]
        addr_off = [getattr(tuser, 'addr_offset{:d}'.format(i)) for i in range(bin(tuser.sop).count("1"))]

        if self._rq_inframe:
            if eop_pos:
                self.handle_request(self._rq_inframe.append(tdata, eop_pos[0] + 1))
                self._rq_inframe = None
                eop_pos.pop(0)
            else:
                self._rq_inframe.append(tdata, 16)

        while sop_pos:
            meta = (fbe.pop(0), lbe.pop(0), addr_off.pop(0))
            dwords = (eop_pos[0] if eop_pos else (self._rq_width // 32 - 1)) - sop_pos[0] * 4 + 1
            self._rq_inframe = Frame(meta).append(tdata >> (sop_pos[0] * (self._rq_width // (2**2))), dwords)
            if eop_pos:
                self.handle_request(self._rq_inframe)
                self._rq_inframe = None
                eop_pos.pop(0)
            sop_pos.pop(0)

    def handle_request(self, req):
        fbe, lbe, addr_offset = req.meta
        header = RQHeader.deserialize(req.data)
        payload = bytes(byte_serialize(req.data >> len(header), header.dword_count * 4))

        addr = header.addr << 2
        byte_count = header.dword_count * 4

        if header.req_type == 1:
            self._ram.w(addr, payload)
            self._log.debug(f"Write addr: {addr:#010x} dwords: {header.dword_count: 3} payload: {payload.hex()}")
        elif header.req_type == 0:
            d = self._ram.r(addr, byte_count)
            self._log.debug(f"Read  addr: {addr:#010x} dwords: {header.dword_count: 3} payload: {d.hex()}")
            self._q.put_nowait((header, req.meta, d))
        else:
            raise NotImplementedError

    async def handle_response(self):
        while True:
            request, req_meta, data = await self._q.get()
            req_fbe, req_lbe, req_addr_offset = req_meta
            dword_count = request.dword_count + 3

            header = RCHeader()
            header.tag = request.tag
            header.dword_count = request.dword_count
            # 15.bit_count() # only in Python 3.10 and newer can be used below
            # TODO: Check IO and CFG transfers
            header.byte_count = (
                request.dword_count * 4
                - (4 - numberOfSetBits(req_fbe))
                - ((4 - numberOfSetBits(req_fbe)) if request.dword_count > 1 else 0)
            )
            header.request_completed = 1
            # TODO: for multiple completions must be updated
            #       FBE is only applied in first completion
            header.addr = (request.addr << 2) + fbe2offset(req_fbe)
            user = RCUser()
            user.sop = 1
            user.eop = 0
            user.eop0 = dword_count - 1

            tdata = concat(
                [(header.serialize(), len(header))]
                + [(byte_deserialize(data), len(data) * 8)]
            )
            while dword_count > 0:
                tkeep = bitmask(self._rq_width // 32)
                if dword_count <= self._rq_width // 32:
                    user.eop = 1
                    user.eop_pos0 = dword_count
                    tkeep = bitmask(dword_count)
                await self._rc.write({"TDATA": tdata & bitmask(self._rq_width), "TUSER": user.serialize(), "TKEEP": tkeep}, sync=False)

                user.sop = 0
                tdata >>= self._rq_width
                dword_count -= self._rq_width // 32
