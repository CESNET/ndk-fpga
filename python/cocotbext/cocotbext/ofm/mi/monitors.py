# monitors.py: MIMonitor
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <Ondrej.Schwarz@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

from cocotb_bus.monitors import BusMonitor
from cocotb.triggers import RisingEdge
from cocotbext.ofm.utils.signals import get_signal_value_in_bytes
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
                addr_bytes = get_signal_value_in_bytes(self.bus.addr)
                be = self.bus.be.value
                be.big_endian = False
                be_int = int.from_bytes(be.buff, 'little')

                recv_trans = MiTransaction()
                recv_trans.trans_type = MiTransactionType.Request
                recv_trans.addr = int.from_bytes(addr_bytes, 'little')
                recv_trans.be = be_int

                self.read_transactions.append(recv_trans)

            if self.bus.drdy.value == 1:
                if len(self.read_transactions) == 0:
                    raise RuntimeError("Received reponse without request.")

                drd_bytes = get_signal_value_in_bytes(self.bus.drd)

                recv_trans = self.read_transactions.pop(0)

                recv_trans.data = filter_bytes_by_bitmask(drd_bytes, recv_trans.be)

                self.log.debug(f"ITEM {self._item_cnt}")
                self.log.debug(f"ADDR {hex(recv_trans.addr)}")
                self.log.debug(f"DRD  {recv_trans.data.hex()}")

                self._recv(recv_trans)
                self._item_cnt += 1

            if self.bus.wr.value == 1 and self.bus.ardy.value == 1:
                dwr_bytes = get_signal_value_in_bytes(self.bus.dwr)
                addr_bytes = get_signal_value_in_bytes(self.bus.addr)

                be = self.bus.be.value
                be.big_endian = False
                be_int = int.from_bytes(be.buff, 'little')

                dwr_recv = b''
                be_list = [*be]
                first_be = be_list.index(1)
                last_be = (be_list+[0]).index(0, first_be)  # ensures there is at least one zero
                dwr_recv = dwr_bytes[first_be:last_be]

                self.log.debug(f"ITEM {self._item_cnt}")
                self.log.debug(f"ADDR {addr_bytes.hex()}")
                self.log.debug(f"DWR  {dwr_bytes.hex()}")
                self.log.debug(f"BE   {be_int}")

                recv_trans = MiTransaction()
                recv_trans.trans_type = MiTransactionType.Response
                recv_trans.addr = int.from_bytes(addr_bytes, 'little')
                recv_trans.data = dwr_recv
                recv_trans.be = be_int

                self._recv(recv_trans)
                self._item_cnt += 1
