import operator
from functools import reduce

import cocotb
from cocotb.queue import Queue

from ..utils import concat, SerializableHeader


def byte_serialize(data, length):
    return [(data >> (8 * i)) & 0xFF for i in range(length)]


def byte_deserialize(data):
    return reduce(
        operator.or_, [(data[i] & 0xFF) << (8 * i) for i in range(len(data))], 0
    )


class RequestHeader(SerializableHeader):
    items = list(zip(
        [
            'at', 'addr', 'dword_count', 'type', 'poisoned_request',
            'req_id', 'tag', 'completer_id', 'req_id_en', 'tc', 'attr', 'force_ecrc',
        ],
        [2, 62, 11, 4, 1, 16, 8, 16, 1, 3, 3, 1],
    ))


class CompletionHeader(SerializableHeader):
    items = list(zip(
        [
            'addr', 'error_code', 'byte_count', 'locked_read_completion',
            'request_completed', 'res1', 'dword_count', 'completion_status',
            'poisoned_completion', 'res2', 'requester_id', 'tag', 'completer_id',
            'res3', 'tc', 'attr', 'res4',
        ],
        [12, 4, 13, 1, 1, 1, 11, 3, 1, 1, 16, 8, 16, 1, 3, 3, 1],
    ))


class RqUser(SerializableHeader):
    items = list(zip(
        [
            'first_be0', 'first_be1', 'last_be0', 'last_be1', 'addr_offset0',
            'addr_offset1', 'sop', 'sop0', 'sop1', 'eop', 'eop0', 'eop1',
            'discontinue', 'tph_present', 'tph_type', 'tph_st_tag',
            'tph_indirect_tag_en', 'seq_num0', 'seq_num1', 'parity',
        ],
        [4, 4, 4, 4, 2, 2, 2, 2, 2, 2, 4, 4, 1, 2, 4, 16, 2, 6, 6, 64],
    ))


class RcUser(SerializableHeader):
    items = list(zip(
        [
            'be', 'sop', 'sop0', 'sop1', 'sop2', 'sop3',
            'eop', 'eop0', 'eop1', 'eop2', 'eop3', 'discontinue', 'parity'
        ],
        [64, 4, 2, 2, 2, 2, 4, 4, 4, 4, 4, 1, 64],
    ))


def bm(bits):
    return (2**bits) - 1


def numberOfSetBits(i):
    i = i - ((i >> 1) & 0x55555555)
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333)
    return (((i + (i >> 4) & 0xF0F0F0F) * 0x1010101) & 0xFFFFFFFF) >> 24


class Frame(object):
    def __init__(self, meta):
        self.meta = meta
        self.data = 0
        self.dwords = 0

    def append(self, data, dwords):
        self.data |= (data & bm(dwords * 32)) << (self.dwords * 32)
        self.dwords += dwords
        return self


class Axi4SRequester:
    def __init__(self, ram, rq_driver, rc_driver, rq_monitor):
        self._verbosity = 0
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

        rq_monitor.add_callback(self.handle_rq_transaction)

        cocotb.start_soon(self.handle_response())

    def handle_rq_transaction(self, transaction):
        tuser = RqUser.deserialize(int.from_bytes(transaction['TUSER'], byteorder='big'))
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
        header = RequestHeader.deserialize(req.data)
        payload = byte_serialize(req.data >> len(header), header.dword_count * 4)

        addr = header.addr << 2
        byte_count = header.dword_count * 4

        if header.type == 1:
            self._ram.w(addr, payload)
            if self._verbosity:
                print(type(self).__name__, "Write addr:", hex(addr), "dword_count:", header.dword_count, "payload:", payload)
            return

        elif header.type == 0:
            d = self._ram.r(addr, byte_count)
            if self._verbosity:
                print(type(self).__name__, "Read  addr:", hex(addr), "dword_count:", header.dword_count, header.tag, "payload:", list(d))
            self._q.put_nowait((header, req.meta, d))

    async def handle_response(self):
        while True:
            request, req_meta, data = await self._q.get()
            req_fbe, req_lbe, req_addr_offset = req_meta
            dword_count = request.dword_count + 3

            header = CompletionHeader()
            header.tag = request.tag
            header.dword_count = request.dword_count
            # 15.bit_count() # only in Python 3.10 and newer can be used below
            # TODO: Check IO and CFG transfers
            header.bytes = (
                request.dword_count * 4
                - (4 - numberOfSetBits(req_fbe))
                - ((4 - numberOfSetBits(req_fbe)) if request.dword_count > 1 else 0)
            )
            header.request_completed = 1
            header.addr = 0  # Info: increment for each consequent completion
            user = RcUser()
            user.sop = 1
            user.eop = 0
            user.eop0 = dword_count - 1

            tdata = concat(
                [(header.serialize(), len(header))]
                + [(byte_deserialize(data), len(data) * 8)]
            )
            while dword_count > 0:
                tkeep = bm(self._rq_width // 32)
                if dword_count < self._rq_width // 32:
                    user.eop = 1
                    user.eop_pos0 = dword_count
                    tkeep = bm(dword_count)
                await self._rc.write({"TDATA": tdata & bm(self._rq_width), "TUSER": user.serialize(), "TKEEP": tkeep}, sync=False)

                user.sop = 0
                tdata >>= self._rq_width
                dword_count -= self._rq_width // 32
