import cocotb
import cocotb.queue
from cocotb.triggers import Event, RisingEdge

from ..utils import concat, SerializableHeader


class RequestHeaderEmpty(SerializableHeader):
    items = list(zip([], []))


class RequestHeader(SerializableHeader):
    items = list(zip(
        ['addr', 'length', 'type', 'res1', 'req_id', 'tag', 'func', 'bar', 'barap', 'res2'],
        [64, 11, 4, 1, 16, 8, 8, 3, 6, 7],
    ))


class RequestUser(SerializableHeader):
    items = list(zip(
        ['firstBe', 'lastBe', 'byte_en', 'sop', 'discontinue', 'tph_present', 'tph_type', 'tph_st_tag', 'parity'],
        [4, 4, 32, 1, 1, 1, 2, 8, 32],
    ))


class RequestUser512(SerializableHeader):
    items = list(zip(
        ['firstBe', 'firstBe1', 'lastBe', 'lastBe1', 'res1', 'sop', 'res2'],
        [4, 4, 4, 4, 64, 1, 0],
    ))


class CompletionHeader(SerializableHeader):
    items = list(zip(
        [
            'lower_address', 'r1', 'at', 'r2', 'byte_count', 'lrc', 'r3',
            'dword_count', 'completion_status', 'poisoned', 'r4', 'rid',
            'tag', 'cid', 'cid_en', 'tc', 'attr', 'ecrc'
        ],
        [7, 1, 2, 6, 13, 1, 2, 11, 3, 1, 1, 16, 8, 16, 1, 3, 3, 1],
    ))


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
        if self._cc_inframe is None:
            h = len(CompletionHeader()) // 8
            hdrbytes, data = data[:h], data[h:]
            self._cc_inframe = CompletionHeader.deserialize(int.from_bytes(hdrbytes, byteorder='little'))

        hdr = self._cc_inframe

        trigger, item, req_data = self._read_requests[hdr.tag]
        addr, byte_count, req_type, orig_data = item

        # Splitted completion for request
        is_first = len(req_data) == 0
        is_last = len(req_data) + len(data) >= byte_count

        off_s = addr % 4 if is_first else 0
        off_e = byte_count - len(req_data) if is_last and tlast else len(data)
        req_data.extend(data[off_s:off_s + off_e])

        if tlast:
            self._cc_inframe = None
            if is_last:
                del self._read_requests[hdr.tag]
                trigger.set(req_data)
                self._tag_queue.put_nowait(hdr.tag)

    async def _cq_req(self, addr, byte_count, req_type=0, data=[], tag=None, sync=True):
        header_empty = RequestHeaderEmpty()
        header = RequestHeader()
        user = RequestUser() if self._axi_width != (512 // 8) else RequestUser512()

        user.firstBe = [0xF, 0xE, 0xC, 0x8][addr % 4]
        user.lastBe = [0xF, 0x1, 0x3, 0x7][(addr + byte_count) % 4]
        user.sop = 1

        dwords = (addr % 4 + byte_count + 3) // 4
        if dwords <= 1:
            user.firstBe &= user.lastBe
            user.lastBe = 0

        if req_type == 1:
            assert len(data) == byte_count
            data = [0] * (addr % 4) + data + [0] * (-(addr + byte_count) % 4)

        if tag is not None:
            header.tag = tag
        header.barap = 26
        header.addr = addr & ~3
        header.length = dwords
        header.type = req_type

        while len(data) or len(header):
            cnt = min(self._axi_width - len(header) // 8, len(data))
            tdata = concat([(header.serialize(), len(header))] + list(zip(data[:cnt], [8] * cnt)))
            tuser = user.serialize()
            tkeep = 2**(cnt // 4 + len(header) // 32) - 1
            await self._cq.write({"TDATA": tdata, "TUSER": tuser, "TKEEP": tkeep}, sync=sync)

            header = header_empty
            user.sop = 0
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
