# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#            Daniel Kondys <kondys@cesnet.cz>

from ..utils import numberOfSetBits, bitmask, byte_serialize
from .PcieHeaders import RQHeader, RCHeader, RQUser, fbe2offset
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
        self._rq_width = len(rq_monitor.bus.TDATA)

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
