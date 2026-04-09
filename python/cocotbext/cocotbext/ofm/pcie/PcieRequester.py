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
    """
    def __init__(self, ram, rq_driver, rc_driver, rq_monitor):
        self._ram = ram
        self._rq = rq_driver
        self._rc = rc_driver

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
        self._q.put_nowait((hdr, d))

    def handle_wr_request(self, data, addr):
        """Writes the given data to RAM at the specified address."""
        self._ram.w(addr, data)
        self._log.debug(f"Write to address: {addr:#010x} length: {len(data):3} data: {data.hex()}")

    @abstractmethod
    def hdr_req2compl(self, rq_hdr):
        """
        Create a completion header from the given request header.

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
        """
        while True:
            rq_hdr, data = await self._q.get()
            # TODO: split response into multiple transactions
            rc_hdr = self.hdr_req2compl(rq_hdr)
            tr = self.prep_response_tr(rc_hdr, data)
            self._rc.append(tr)
