import cocotb
from cocotb.queue import Queue

from ..utils import concat, deconcat, SerializableHeader


class CompletionHeaderEmpty(SerializableHeader):
    items = list(zip([], []))


class RequestHeader(SerializableHeader):
    items = list(zip(
        [
            'addr', 'fbe', 'lbe', 'tag_l', 'req_id', 'dwords', 'res',
            'attr_l', 'pois_req', 'ecrc', 'res', 'attr_h', 'tag_m',
            'prio', 'tag_h', 'tlp_type', 'addr_len', 'req_type'
        ],
        [64, 4, 4, 8, 16, 10, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 2],
    ))


class CompletionHeader(SerializableHeader):
    items = list(zip(
        [
            'padding', 'low_addr', 'res1', 'tag_l', 'res2', 'byte_cnt',
            'res3', 'compl_stat', 'res4', 'dwords', 'res5', 'attr_l',
            'res6', 'attr_h', 'tag_m', 'res7', 'tag_h', 'tlp_type', 'fmt'
        ],
        [32, 7, 1, 8, 16, 12, 1, 3, 16, 10, 2, 2, 4, 1, 1, 3, 1, 5, 3],
    ))


def numberOfSetBits(i):
    i = i - ((i >> 1) & 0x55555555)
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333)
    return (((i + (i >> 4) & 0xF0F0F0F) * 0x1010101) & 0xFFFFFFFF) >> 24


class AvstBase:
    def __init__(self, cdriver):
        self._cdriver = cdriver
        bus = cdriver.bus

        try:
            self._segs = len(bus.VALID)
        except Exception:
            self._segs = 1

        self._empty_width = len(bus.EMPTY) // self._segs
        self._hdr_width = len(bus.HDR) // self._segs
        self._avst_width = len(bus.DATA) // 8

    async def _send_frame(self, cb, data, header, header_empty):
        _avst_width = self._avst_width // self._segs
        orig_data = data
        seg, dwr, sop, eop, emp, hdr = 0, 0, 0, 0, 0, 0
        end = False
        while not end:
            length = min(_avst_width, len(data))
            begin = len(data) == len(orig_data)
            end = len(data) == length
            dwr |= concat(list(zip(data[:length], [8] * length))) << (seg * _avst_width * 8)
            emp |= (((_avst_width - length) // 4) if length else 0) << (seg * self._empty_width)
            hdr |= (header.serialize() if begin else header_empty.serialize()) << (seg * self._hdr_width)
            sop |= (1 if begin else 0) << seg
            eop |= (1 if end else 0) << seg

            seg += 1
            if seg == self._segs or end:
                await cb(
                    {
                        "DATA": dwr, "HDR": hdr, "SOP": sop, "EOP": eop, "EMPTY": emp, "PREFIX": 0, "BAR_RANGE": 0, "VALID": 2**seg - 1
                    },
                )
                seg, dwr, sop, eop, emp, hdr = 0, 0, 0, 0, 0, 0
            data = data[length:]


class AvstRequester(AvstBase):
    def __init__(self, ram, rq_driver, rc_driver, rq_monitor):
        super().__init__(rc_driver)

        self._verbosity = 0
        self._ram = ram
        self._rq = rq_driver
        self._rc = rc_driver
        self._rqm = rq_monitor

        self._q = Queue()
        self._rq_processing_frame = False
        self._rq_frame = None
        self._rq_pending = 0
        self._rq_pending_dwords = 0
        self._rq_pending_meta = ()

        rq_monitor.add_callback(self.handle_rq_transaction)

        cocotb.start_soon(self.handle_response())

    def handle_rq_transaction(self, transaction):
        header_bytes, data_bytes = transaction
        data = list(data_bytes)
        hdr = RequestHeader.deserialize(int.from_bytes(header_bytes, byteorder="big"))

        # Process only if it is a request (DMA WR or RD)
        if hdr.tlp_type == 0 and hdr.req_type in [0, 1]:
            self.handle_request((hdr, data))

    def handle_request(self, req):
        header, payload = req
        byte_count = header.dwords * 4

        if header.addr_len == 0: # 32-bit address
            addr_h, addr_l = deconcat([header.addr, 32, 32])
            addr = addr_l
        else: # 64-bit address
            addr = header.addr

        if header.req_type == 1: # write
            self._ram.w(addr, payload)
            if self._verbosity:
                print(type(self).__name__, "Write addr:", hex(addr), "dwords:", header.dwords, "payload:", payload)
        elif header.req_type == 0: # read
            d = self._ram.r(addr, byte_count)
            if self._verbosity:
                print(type(self).__name__, "Read addr:", hex(addr), "dwords:", header.dwords, "payload:", list(d))
            self._q.put_nowait((header, d))

    async def handle_response(self):
        while True:
            rq_hdr, data = await self._q.get()
            rq_fbe = rq_hdr.fbe

            header_empty = CompletionHeaderEmpty()
            header = CompletionHeader()
            header.tag_l, header.tag_m, header.tag_h = rq_hdr.tag_l, rq_hdr.tag_m, rq_hdr.tag_h
            header.fmt = int("010", base=2) # Completition with data: "010", Completition withOUT data: "000"
            header.tlp_type = int("01010", base=2) # Completion for LOCKED Memory Read: "01011" (with/without data)
            header.dwords = rq_hdr.dwords
            # 15.bit_count() # only in Python 3.10 and newer can be used below
            # TODO: Check IO and CFG transfers
            header.byte_cnt = (
                header.dwords * 4
                - (4 - numberOfSetBits(rq_fbe))
                - ((4 - numberOfSetBits(rq_fbe)) if header.dwords > 1 else 0)
            )
            header.compl_stat = 1
            # WTF is this?
            header.low_addr = 0  # Info: increment for each consequent completion
            await self._send_frame(self._cdriver.write_rc, data, header, header_empty)
