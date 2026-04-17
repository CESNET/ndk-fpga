# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>

from abc import ABC, abstractmethod
import logging
import random
import cocotb
from cocotb.queue import Queue
from cocotb.triggers import ClockCycles


class PcieRequester(ABC):
    """
    Base class that handles PCIe requests and generates responses.

    Attributes:
    ram: memory, such as RAM from cocotbext.ofm.utils
    rc_driver: to drive responses onto the appropriate interface
    rq_monitor: to receive requests from the appropriate interface
    mps: Max Payload Size in bytes (default 256 bytes)
    rcb: Read Completion Boundary in bytes (default 64 bytes)
    cpl_dly: delay of Read Completions in number of clock cycles
    """
    def __init__(self, ram, rq_driver, rc_driver, rq_monitor, mps=256, rcb=64, cpl_dly=10):
        self._ram = ram
        self._rq = rq_driver
        self._rc = rc_driver
        self._mps = mps  # Max Payload Size in bytes
        self._rcb = rcb  # Read Completion Boundary in bytes
        self._cpl_dly = cpl_dly

        # Per-tag queues: dict[tag, Queue]
        self._tag_queues = {}

        self._log = logging.getLogger(__name__)

        rq_monitor.add_callback(self.handle_rq_transaction)

        cocotb.start_soon(self.handle_response())

    @abstractmethod
    def handle_rq_transaction(self, transaction):
        """
        Process PCIe request transactions received from the monitor.

        To be reimplemented according to the specific PCIe header type.
        Write to or read data from the memory using self.handle_rd_request() or handle_wr_request() methods.
        """
        raise NotImplementedError

    @abstractmethod
    def tag_from_hdr(self, hdr):
        """
        Extract the tag value from the request header.

        Args:
            hdr: The request header (format depends on the specific implementation)

        Returns:
            int: The tag value extracted from the header

        To be reimplemented according to the specific PCIe header type.
        """
        raise NotImplementedError

    def handle_rd_request(self, hdr, addr, length):
        """
        Reads data from RAM and queues individual completions for response handling.
        Completions are split at queue time to allow interleaving between tags.
        """
        d = self._ram.r(addr, length)
        self._log.debug(f"Read from address: {addr:#010x} length: {length:3} data: {d.hex()}")

        # Split into partial completions and queue them
        self._queue_completions(hdr, d, addr)

    def _queue_completions(self, hdr, data, addr):
        """
        Split a read request into individual completions and queue them.

        Args:
            hdr: The request header
            data: The data read from RAM
            addr: The starting address
        """
        q = Queue()
        tag = self.tag_from_hdr(hdr)

        total_bytes = len(data)
        bytes_remaining = total_bytes
        current_addr = addr
        offset = 0
        is_first = True

        while bytes_remaining > 0:
            # Calculate the next RCB boundary
            next_rcb_boundary = ((current_addr // self._rcb) + 1) * self._rcb

            if is_first:
                # First completion: can go up to MPS or next RCB boundary, whichever is smaller
                max_first_payload = min(self._mps, next_rcb_boundary - current_addr)
                payload_bytes = min(bytes_remaining, max_first_payload)
                lower_addr = addr
                is_first = False
            else:
                # Subsequent completions: start at RCB boundary, limited by MPS
                payload_bytes = min(bytes_remaining, self._mps)
                lower_addr = current_addr

            is_last = (payload_bytes >= bytes_remaining)

            # Create completion header
            rc_hdr = self.hdr_req2compl(
                hdr,
                byte_count=bytes_remaining,
                lower_address=lower_addr,
                is_last=is_last,
                payload_bytes=payload_bytes
            )

            # Extract payload data for this completion
            completion_data = data[offset:offset + payload_bytes]

            # Create and queue completion
            completion = self.prep_response_tr(rc_hdr, completion_data)
            q.put_nowait(completion)

            # Update tracking variables
            bytes_remaining -= payload_bytes
            offset += payload_bytes
            current_addr += payload_bytes

        self._tag_queues[tag] = q

    def handle_wr_request(self, data, addr):
        """Writes the given data to RAM at the specified address."""
        self._ram.w(addr, data)
        self._log.debug(f"Write to address: {addr:#010x} length: {len(data):3} data: {data.hex()}")

    @abstractmethod
    def hdr_req2compl(self, rq_hdr, byte_count=None, lower_address=None, is_last=True, payload_bytes=None):
        """
        Create a completion header from the given request header.

        Args:
            rq_hdr: The original request header
            byte_count: Total remaining bytes including this completion (for split completions)
            lower_address: Lower address for this completion (RCB-aligned for non-first completions)
            is_last: True if this is the final completion in a split sequence
            payload_bytes: Number of payload bytes in this completion

        To be reimplemented according to the specific PCIe header type.
        """
        raise NotImplementedError

    def prep_response_tr(self, hdr, data, **kwargs):
        """Allows the user to modifiy the response transaction sent to the driver."""
        return hdr, data

    async def handle_response(self):
        """
        Processes queued completions and sends them to the driver.
        Completions from different tags are interleaved randomly while
        maintaining ordering within each tag.
    """
        # Wait until at least one tag has data
        while not self._tag_queues or all(q.empty() for q in self._tag_queues.values()):
            await ClockCycles(self._rc.clock, self._cpl_dly)

        while True:
            # Get list of tags with non-empty queues
            ready_tags = [tag for tag, q in self._tag_queues.items() if not q.empty()]

            if ready_tags:
                # Randomly select a tag and send one completion
                selected_tag = random.choice(ready_tags)
                completion = await self._tag_queues[selected_tag].get()
                self._rc.append(completion)

            # Wait until at least one tag has data
            while not self._tag_queues or all(q.empty() for q in self._tag_queues.values()):
                await ClockCycles(self._rc.clock, self._cpl_dly)
