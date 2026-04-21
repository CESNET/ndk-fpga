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

    def __init__(self, ram, rq_driver, rc_driver, rq_monitor, mps=256, rcb=64, cpl_split_mode=PcieRequester.SPLIT_MAX):
        super().__init__(ram, rq_driver, rc_driver, rq_monitor, mps, rcb, cpl_split_mode)
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
        fbe, lbe, addr_off = req.meta # address offset is driven low by FW

        addr = header.addr << 2
        # Add FBE offset to address (indicates byte offset)
        try:
            fbe_offset = fbe2offset(fbe)
            addr += fbe_offset
        except ValueError:
            fbe_offset = 0 # leave address as is when hdr.fbe==0 (-> read requests)

        byte_length = (
            header.dword_count * 4
            - (4 - numberOfSetBits(fbe))
            - ((4 - numberOfSetBits(lbe)) if header.dword_count > 1 else 0)
        )

        if header.req_type == 1:
            payload = bytes(payload[fbe_offset:fbe_offset + byte_length])
            self.handle_wr_request(data=payload, addr=addr)
        elif header.req_type == 0:
            self.handle_rd_request(hdr=(header, req.meta), addr=addr, length=byte_length)
        else:
            raise NotImplementedError

    def tag_from_hdr(self, hdr):
        """Extract the tag value from the AXI4S request header."""
        req_hdr, meta = hdr  # hdr is a tuple (header, metadata)
        return req_hdr.tag

    def hdr_req2compl(self, rq_hdr, byte_count=None, lower_address=None, is_last=True, payload_bytes=None):
        """
        Creates a completion header from the given request header.

        Args:
            rq_hdr: The original request header (tuple of header and metadata for AXI4S)
            byte_count: Total remaining bytes including this completion (for split completions)
            lower_address: Lower address for this completion (RCB-aligned for non-first completions)
            is_last: True if this is the final completion in a split sequence
            payload_bytes: Number of payload bytes in this completion
        """
        req_hdr, meta = rq_hdr  # AXI speciality - some data are in header, some in metadata (tuser)
        req_fbe, req_lbe, req_addr_offset = meta
        rc_hdr = RCHeader()
        rc_hdr.tag = req_hdr.tag

        # Calculate dword_count from payload_bytes
        if payload_bytes is not None:
            rc_hdr.dword_count = (payload_bytes + 3) // 4  # Round up to dwords
        else:
            rc_hdr.dword_count = req_hdr.dword_count

        # Set byte_count - total remaining bytes including this completion
        if byte_count is not None:
            rc_hdr.byte_count = byte_count
        else:
            # TODO: Check IO and CFG transfers
            rc_hdr.byte_count = (
                req_hdr.dword_count * 4
                - (4 - numberOfSetBits(req_fbe))
                - ((4 - numberOfSetBits(req_lbe)) if req_hdr.dword_count > 1 else 0)
            )

        # Set request_completed - only 1 on the final completion
        rc_hdr.request_completed = 1 if is_last else 0

        # Set lower address
        if lower_address is not None:
            # For split completions: first uses original address, subsequent are RCB-aligned
            rc_hdr.addr = lower_address & 0xFFF  # 12-bit address field
        else:
            # Same address correction as above in handle_rq_transaction()
            addr = req_hdr.addr << 2
            try:
                addr += fbe2offset(req_fbe)
            except ValueError:
                pass
            rc_hdr.addr = addr

        return rc_hdr
