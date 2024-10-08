# monitors.py: MIMonitor
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <Ondrej.Schwarz@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

from cocotb_bus.monitors import BusMonitor
from cocotb.triggers import RisingEdge
from cocotbext.ofm.utils.signals import get_signal_value_in_bytes


class MIMasterMonitor(BusMonitor):
    """Master monitor intended for monitoring the MI BUS OUTPUT side.

    Atributes:
        item_cnt(int): number of items recieved.
        _clk_re(cocotb.triggers.RisingEdge): object used for awaiting the rising edge of clock signal.
        _utils(MIUtils): object with general MI Utilities.
        addr_width(int): width of ADDR port in bytes.
        data_width(int): width of DATA port in bytes.

    """

    _signals = ["addr", "dwr", "be", "wr", "rd", "ardy", "drd", "drdy"]
    _optional_signals = ["mwr"]

    def __init__(self, entity, name, clock, array_idx=None) -> None:
        super().__init__(entity, name, clock, array_idx=array_idx)
        self.item_cnt = 0
        self._clk_re = RisingEdge(self.clock)
        self.addr_width = len(self.bus.addr) // 8
        self.data_width = len(self.bus.dwr) // 8

    async def _monitor_recv(self):
        """Recieve function for the cocotb testbench"""

        # Avoid spurious object creation by recycling
        clk_re = RisingEdge(self.clock)

        while True:
            await clk_re

            if self.in_reset:
                continue

            if self.bus.wr.value == 1 and self.bus.ardy.value == 1:
                dwr_bytes = get_signal_value_in_bytes(self.bus.dwr)
                addr_bytes = get_signal_value_in_bytes(self.bus.addr)

                be = self.bus.be.value
                be.big_endian = False
                be_int = int.from_bytes(be.buff, 'little')

                dwr_recv = b''
                be_list = list()
                be_list[0:len(be)] = be
                first_be = be_list.index(1)
                last_be = (be_list + [0]).index(0, first_be)
                dwr_recv = dwr_bytes[first_be:last_be]

                self.log.debug(f"ITEM     {self.item_cnt}")
                self.log.debug(f"OUT_ADDR {addr_bytes.hex()}")
                self.log.debug(f"OUT_DWR  {dwr_bytes.hex()}")
                self.log.debug(f"OUT_BE   {be_int}")

                self._recv((int.from_bytes(addr_bytes, 'little'), int.from_bytes(dwr_recv, 'little'), be_int))
                self.item_cnt += 1


class MISlaveMonitor(BusMonitor):
    """Slave monitor intended for monitoring the MI BUS INPUT side.

    Atributes:
        _signals(list): mandatory signals of the MI BUS.
        _optional_signals(list): any other usefull signal that may be part of the MI BUS.
        item_cnt(int): number of items recieved.
        _clk_re(cocotb.triggers.RisingEdge): object used for awaiting the rising edge of clock signal.
        _utils(MIUtils): object with general MI Utilities.
        addr_width(int): width of ADDR port in bytes.
        data_width(int): width of DATA port in bytes.

    """

    _signals = ["addr", "dwr", "be", "wr", "rd", "ardy", "drd", "drdy"]
    _optional_signals = ["mwr"]

    def __init__(self, entity, name, clock, array_idx=None):
        super().__init__(entity, name, clock, array_idx=array_idx)
        self.item_cnt = 0
        self._clk_re = RisingEdge(self.clock)
        self.addr_width = len(self.bus.addr) // 8
        self.data_width = len(self.bus.dwr) // 8

    async def _monitor_recv(self):
        """Recieve function for the cocotb testbench."""

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

            if self.bus.drdy.value == 1:
                drd_bytes = get_signal_value_in_bytes(self.bus.drd)

                self.log.debug(f"ITEM     {self.item_cnt}")
                self.log.debug(f"IN_ADDR {addr_bytes.hex()}")
                self.log.debug(f"IN_DRD  {drd_bytes.hex()}")

                self._recv((int.from_bytes(addr_bytes, 'little'), int.from_bytes(drd_bytes, 'little'), be_int))

                self.item_cnt += 1
