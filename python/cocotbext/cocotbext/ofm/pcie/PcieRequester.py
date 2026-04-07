# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>

from abc import ABC, abstractmethod
import logging
import cocotb
from cocotb.queue import Queue


class PcieRequester(ABC):
    """
    Base class that handles PCIe requests and generates responses.

    Attributes:
    ram: memory, such as RAM from cocotbext.ofm.utils
    rc_driver: to drive responses onto the appropriate interface
    rq_monitor: to receive requests from the appropriate interface
    mps: Max Payload Size in bytes (default 256 bytes)
    rcb: Read Completion Boundary in bytes (default 64 bytes)
    """
    def __init__(self, ram, rq_driver, rc_driver, rq_monitor, mps=256, rcb=64):
        self._ram = ram
        self._rq = rq_driver
        self._rc = rc_driver
        self._mps = mps  # Max Payload Size in bytes
        self._rcb = rcb  # Read Completion Boundary in bytes

        self._q = Queue()

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

    def handle_rd_request(self, hdr, addr, length):
        """Reads data from RAM and queues it (and the original header) for response handling."""
        d = self._ram.r(addr, length)
        self._log.debug(f"Read from address: {addr:#010x} length: {length:3} data: {d.hex()}")
        self._q.put_nowait((hdr, d, addr))

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
        Processes queued read requests from which it generates completions.

        Gets request header and read data from the queue, lets the user create a completion header, and sends it to the driver.
        Supports split completions for large responses based on Max Payload Size (MPS) and Read Completion Boundary (RCB).
        Per PCIe spec, completions must not cross RCB boundaries.
        """
        while True:
            rq_hdr, data, addr = await self._q.get()
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

                # Extract payload data for this completion
                completion_data = data[offset:offset + payload_bytes]

                # Create completion header
                rc_hdr = self.hdr_req2compl(
                    rq_hdr,
                    byte_count=bytes_remaining,
                    lower_address=lower_addr,
                    is_last=is_last,
                    payload_bytes=payload_bytes
                )

                tr = self.prep_response_tr(rc_hdr, completion_data)
                self._rc.append(tr)

                # Update tracking variables
                bytes_remaining -= payload_bytes
                offset += payload_bytes
                current_addr += payload_bytes
