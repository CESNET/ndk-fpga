# monitors.py: MIMonitor
# Copyright (C) 2024-2026 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <ondrejschwarz@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

from cocotbext.ofm.base.monitors import BusMonitor
from cocotb.triggers import RisingEdge
from cocotbext.ofm.mi.transaction import MiTransaction, MiTransactionType
from cocotbext.ofm.utils.signals import filter_bytes_by_bitmask


class MIMonitor(BusMonitor):
    """Monitor intended for monitoring both sides of the MI bus."""

    _signals = ["addr", "dwr", "be", "wr", "rd", "ardy", "drd", "drdy"]
    _optional_signals = ["mwr"]

    def __init__(self, *args, **kwargs) -> None:
        super().__init__(*args, **kwargs)
        self._item_cnt = 0
        self._clk_re = RisingEdge(self.clock)
        self._addr_width = len(self.bus.addr) // 8
        self._data_width = len(self.bus.dwr) // 8
        self.read_transactions = list()

    @property
    def item_cnt(self) -> int:
        """Number of items received."""
        return self._item_cnt

    @property
    def addr_width(self) -> int:
        """Width of ADDR port in bytes."""
        return self._addr_width

    @property
    def data_width(self) -> int:
        """Width of DATA port in bytes."""
        return self._data_width

    async def _monitor_recv(self):
        """Receive function for the cocotb testbench"""

        # Avoid spurious object creation by recycling
        clk_re = RisingEdge(self.clock)

        while True:
            await clk_re

            if self.in_reset:
                continue

            if self.bus.rd.value == 1 and self.bus.ardy.value == 1:
                addr_bytes = self.bus.addr.value.to_bytes(byteorder="little")
                be = self.bus.be.value
                be_int = be.to_unsigned()

                recv_trans = MiTransaction()
                recv_trans.trans_type = MiTransactionType.Request
                recv_trans.addr = int.from_bytes(addr_bytes, 'little')
                recv_trans.be = be_int

                self.read_transactions.append(recv_trans)

            if self.bus.drdy.value == 1:
                if len(self.read_transactions) == 0:
                    raise RuntimeError("Received reponse without request.")

                drd_bytes = self.bus.drd.value.to_bytes(byteorder="little")

                recv_trans = self.read_transactions.pop(0)

                recv_trans.data = filter_bytes_by_bitmask(drd_bytes, recv_trans.be)

                self.log.debug(f"ITEM {self._item_cnt}")
                self.log.debug(f"ADDR {hex(recv_trans.addr)}")
                self.log.debug(f"DRD  {recv_trans.data.hex()}")

                self._recv(recv_trans)
                self._item_cnt += 1

            if self.bus.wr.value == 1 and self.bus.ardy.value == 1:
                dwr_bytes = self.bus.dwr.value.to_bytes(byteorder="little")
                addr_bytes = self.bus.addr.value.to_bytes(byteorder="little")

                be = self.bus.be.value
                be_int = be.to_unsigned()

                self.log.debug(f"ITEM {self._item_cnt}")
                self.log.debug(f"ADDR {addr_bytes.hex()}")
                self.log.debug(f"DWR  {dwr_bytes.hex()}")
                self.log.debug(f"BE   {be_int}")

                recv_trans = MiTransaction()
                recv_trans.trans_type = MiTransactionType.Response
                recv_trans.addr = int.from_bytes(addr_bytes, 'little')
                recv_trans.data = filter_bytes_by_bitmask(dwr_bytes, be_int)
                recv_trans.be = be_int

                self._recv(recv_trans)
                self._item_cnt += 1
