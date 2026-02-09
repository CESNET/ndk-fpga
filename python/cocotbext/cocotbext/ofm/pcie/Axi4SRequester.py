# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#            Daniel Kondys <kondys@cesnet.cz>

from ..utils import concat, numberOfSetBits, bitmask, byte_serialize, byte_deserialize
from .PcieHeaders import RQHeader, RCHeader, RQUser, RCUser, fbe2offset
from .PcieRequester import PcieRequester


class Frame(object):
    def __init__(self, meta):
        self.meta = meta
        self.data = 0
        self.dwords = 0

    def append(self, data, dwords):
        self.data |= (data & bitmask(dwords * 32)) << (self.dwords * 32)
        self.dwords += dwords
        return self


class Axi4SRequester(PcieRequester):
    """Handles PCIe requests on the PCIe-specific AXI4-Streaming interface."""

    def __init__(self, ram, rq_driver, rc_driver, rq_monitor):
        super().__init__(ram, rq_driver, rc_driver, rq_monitor)
        self._rq_inframe = False
        self._rq_width = len(self._rq.bus.TDATA)

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
        header = RQHeader.deserialize(req.data)
        payload = bytes(byte_serialize(req.data >> len(header), header.dword_count * 4))

        addr = header.addr << 2
        if header.req_type == 1:
            self.handle_wr_request(data=payload, addr=addr)
        elif header.req_type == 0:
            self.handle_rd_request(hdr=(header, req.meta), addr=addr, length=header.dword_count*4)
        else:
            raise NotImplementedError

    def hdr_req2compl(self, rq_hdr):
        req_hdr, meta = rq_hdr # AXI speciality - some data are in header, some in metadata (tuser)
        req_fbe, req_lbe, req_addr_offset = meta
        rc_hdr = RCHeader()
        rc_hdr.tag = req_hdr.tag
        rc_hdr.dword_count = req_hdr.dword_count
        # TODO: Check IO and CFG transfers
        rc_hdr.byte_count = (
            req_hdr.dword_count * 4
            - (4 - numberOfSetBits(req_fbe))
            - ((4 - numberOfSetBits(req_fbe)) if req_hdr.dword_count > 1 else 0)
        )
        # TODO: support multiple completions
        rc_hdr.request_completed = 1
        # TODO: for multiple completions must be updated
        #       FBE is only applied in first completion
        rc_hdr.addr = (req_hdr.addr << 2) + fbe2offset(req_fbe)
        return rc_hdr

    async def handle_response(self):
        """
        Need to overload this method to connect (convert) to the AXI driver.

        The driver (self._rc) accepts words (word=dictionary) or AXI transactions.
        As this AXI bus is very specific, we need to provide words.
        Another way would be to write a specific driver for this type of AXI bus.
        """
        while True:
            rq_hdr, data = await self._q.get()
            # TODO: split response into multiple transactions
            rc_hdr = self.hdr_req2compl(rq_hdr)
            dword_count = rc_hdr.dword_count + 3 # 3 DWs of header, equivalent to: len(rc_hdr) // 32

            user = RCUser()
            user.sop = 1
            user.eop = 0
            user.eop0 = dword_count - 1
            # PCIe header on AXI is prepended to the data
            tdata = concat(
                [(rc_hdr.serialize(), len(rc_hdr))]
                + [(byte_deserialize(data), len(data) * 8)]
            )
            # Send transaction word by word to the driver
            while dword_count > 0:
                word = {}
                tkeep = bitmask(self._rq_width // 32)
                if dword_count <= self._rq_width // 32:
                    user.eop = 1
                    user.eop_pos0 = dword_count
                    tkeep = bitmask(dword_count)
                self._rc.append({"TDATA": tdata & bitmask(self._rq_width), "TUSER": user.serialize(), "TKEEP": tkeep})

                user.sop = 0
                tdata >>= self._rq_width
                dword_count -= self._rq_width // 32
