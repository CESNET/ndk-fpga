# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#            Martin Spinler <spinler@cesnet.cz>
#            Radek Isa <isa@cesnet.cz>

from ..utils import deconcat, numberOfSetBits, SerializableHeader
from .PcieHeaders import fbe2offset
from .PcieRequester import PcieRequester


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


class AvstRequester(PcieRequester):
    """Handles PCIe requests on the PCIe-specific AVST interface."""

    def __init__(self, ram, rq_driver, rc_driver, rq_monitor, mps=256, rcb=64):
        super().__init__(ram, rq_driver, rc_driver, rq_monitor, mps, rcb)
        self._avst_tr_type = 1 # differentiates transactions for the driver; 0=CQ, 1=RC

    def handle_rq_transaction(self, transaction):
        """Parses the RQ header and writes to or reads from the memory accordingly."""
        header, data_bytes = transaction
        if isinstance(header, bytes):
            hdr = RequestHeader.deserialize(int.from_bytes(header, byteorder="big"))
        elif isinstance(header, RequestHeader):
            hdr = header
        else:
            raise NotImplementedError

        if hdr.addr_len == 0: # 32-bit address
            addr_h, addr_l = deconcat([hdr.addr, 32, 32])
            addr = addr_l
        else: # 64-bit address
            addr = hdr.addr

        # Fiter out MI responses - process if it is a request (DMA WR or RD)
        if hdr.tlp_type == 0:
            if hdr.req_type == 0:
                self.handle_rd_request(hdr=hdr, addr=addr, length=hdr.dwords*4)
            elif hdr.req_type == 1:
                self.handle_wr_request(data=data_bytes, addr=addr)
            else:
                raise NotImplementedError(f"Unsupported REQ type {hdr.req_type}, expected: [0, 1]")

    def hdr_req2compl(self, rq_hdr, byte_count=None, lower_address=None, is_last=True, payload_bytes=None):
        """
        Creates a completion header from the given request header.

        Args:
            rq_hdr: The original request header
            byte_count: Total remaining bytes including this completion (for split completions)
            lower_address: Lower address for this completion (RCB-aligned for non-first completions)
            is_last: True if this is the final completion in a split sequence
            payload_bytes: Number of payload bytes in this completion
        """
        rc_hdr = CompletionHeader()
        rc_hdr.tag_l, rc_hdr.tag_m, rc_hdr.tag_h = rq_hdr.tag_l, rq_hdr.tag_m, rq_hdr.tag_h
        rc_hdr.fmt = int("010", base=2) # Completition with data: "010", Completition withOUT data: "000"
        rc_hdr.tlp_type = int("01010", base=2) # Completion for LOCKED Memory Read: "01011" (with/without data)

        # Calculate dwords from payload_bytes
        if payload_bytes is not None:
            rc_hdr.dwords = (payload_bytes + 3) // 4  # Round up to dwords
        else:
            rc_hdr.dwords = rq_hdr.dwords

        # Set byte_count - total remaining bytes including this completion
        if byte_count is not None:
            rc_hdr.byte_cnt = byte_count
        else:
            # TODO: Check IO and CFG transfers
            rc_hdr.byte_cnt = (
                rc_hdr.dwords * 4
                - (4 - numberOfSetBits(rq_hdr.fbe))
                - ((4 - numberOfSetBits(rq_hdr.fbe)) if rc_hdr.dwords > 1 else 0)
            )

        # Set lower address
        if lower_address is not None:
            # For split completions: first uses original address, subsequent are RCB-aligned
            rc_hdr.low_addr = lower_address & 0x7f
        else:
            if rq_hdr.addr_len == 0: # 32-bit address
                addr_h, addr_l = deconcat([rq_hdr.addr, 32, 32])
                addr = addr_l
            else: # 64-bit address
                addr = rq_hdr.addr
            rc_hdr.low_addr = ((addr) + fbe2offset(rq_hdr.fbe)) & 0x7f

        return rc_hdr

    def prep_response_tr(self, hdr, data, **kwargs):
        """Allows the user to modifiy the response transaction sent to the driver."""
        return hdr, data, self._avst_tr_type
