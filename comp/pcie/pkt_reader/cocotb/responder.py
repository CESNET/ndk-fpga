# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>

from cocotbext.ofm.pcie.PcieRequester import PcieRequester
from cocotbext.ofm.mvb.transaction import MvbTrClassic
from cocotbext.ofm.utils.header import SerializableHeader


# DMA_COMPLETION header from dma_bus_pack.vhd
class DmaDownHdr(SerializableHeader):
    items = [
        ('dma_completion_length', 11),
        ('dma_completion_completed', 1),
        ('dma_completion_tag', 8),
        ('dma_completion_unitid', 8),
    ]


# DMA_REQUEST header from dma_bus_pack.vhd
class DmaUpHdr(SerializableHeader):
    items = [
        ('dma_request_length', 11),
        ('dma_request_type', 1),
        ('dma_request_firstib', 2),
        ('dma_request_lastib', 2),
        ('dma_request_tag', 8),
        ('dma_request_unitid', 8),
        ('dma_request_global', 64),
        ('dma_request_vfid', 8),
        ('dma_request_pasid', 0),
        ('dma_request_pasidvld', 0),
        ('dma_request_relaxed', 1),
    ]


class PprRequester(PcieRequester):
    """Handles PCIe requests for the PCIe Packet Reader module."""

    def __init__(self, ram, rq_driver, rc_driver, rq_monitor, mps=256, rcb=64, cpl_split_mode=PcieRequester.SPLIT_RAND, cpl_dly=10):
        super().__init__(ram, rq_driver, rc_driver, rq_monitor, mps, rcb, cpl_split_mode, cpl_dly)

    def handle_rq_transaction(self, transaction):
        """Parses the RQ header and writes to or reads from the memory accordingly."""
        mvb_hdr = transaction
        dma_uphdr = DmaUpHdr.deserialize(mvb_hdr.data)

        addr = dma_uphdr.dma_request_global + dma_uphdr.dma_request_firstib
        length = dma_uphdr.dma_request_length * 4 - dma_uphdr.dma_request_firstib - dma_uphdr.dma_request_lastib

        # Process only if it is a Read request
        if dma_uphdr.dma_request_type == 0:
            self.handle_rd_request(hdr=dma_uphdr, addr=addr, length=length)
        else:
            raise NotImplementedError

    def tag_from_hdr(self, hdr):
        """Extract the tag value from the DMA request header."""
        return hdr.dma_request_tag

    def hdr_req2compl(self, rq_hdr, byte_count=None, lower_address=None, is_last=True, payload_bytes=None):
        """
        Creates a completion header from the given request header.

        Args:
            rq_hdr: The original request header (DmaUpHdr)
            byte_count: Total remaining bytes including this completion (for split completions)
            lower_address: Lower address for this completion (RCB-aligned for non-first completions)
            is_last: True if this is the final completion in a split sequence
            payload_bytes: Number of payload bytes in this completion
        """
        dma_downhdr = DmaDownHdr()

        # Calculate length in dwords from payload_bytes
        if payload_bytes is not None:
            dma_downhdr.dma_completion_length = (payload_bytes + 3) // 4  # Round up to dwords
        else:
            dma_downhdr.dma_completion_length = rq_hdr.dma_request_length

        # Set dma_completion_completed - only 1 on the final completion
        dma_downhdr.dma_completion_completed = 1 if is_last else 0

        dma_downhdr.dma_completion_tag = rq_hdr.dma_request_tag
        dma_downhdr.dma_completion_unitid = 0 # Not used
        mvb_hdr = MvbTrClassic()
        mvb_hdr.data = dma_downhdr.serialize()
        return mvb_hdr
