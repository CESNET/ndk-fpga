# drivers.py: MIDriver
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <Ondrej.Schwarz@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

from cocotbext.ofm.base.drivers import BusDriver
from cocotbext.ofm.utils.math import ceildiv
from cocotbext.ofm.utils.signals import await_signal_sync


class MIMasterDriver(BusDriver):
    """Master driver intended for the MI BUS that allows sending data to and recieving from the bus.

    Atributes:
        _clk_re(cocotb.triggers.RisingEdge): object used for awaiting the rising edge of clock signal.
        addr_width(int): width of ADDR port in bytes.
        data_width(int): width of DATA port in bytes.
        _addr(int), _dwr(bytearray), _be(int), _wr(int), _rd(int): control signals that are then propagated to the MI BUS.

    """

    _signals = ["addr", "dwr", "be", "wr", "rd", "ardy", "drd", "drdy"]
    _optional_signals = ["mwr"]

    def __init__(self, entity, name, clock, array_idx=None) -> None:
        super().__init__(entity, name, clock, array_idx=array_idx)
        self.addr_width = len(self.bus.addr) // 8
        self.data_width = len(self.bus.dwr) // 8
        self._clear_control_signals()
        self._propagate_control_signals()

    def _clear_control_signals(self) -> None:
        """Sets control signals to default values without sending them to the MI bus."""

        self._addr = 0
        self._dwr = bytearray(self.data_width)
        self._be = 0
        self._wr = 0
        self._rd = 0

    def _propagate_control_signals(self) -> None:
        """Sends value of control signals to the MI bus."""

        self.bus.addr.value = self._addr
        self.bus.dwr.value = int.from_bytes(self._dwr, 'little')
        self.bus.be.value = self._be
        self.bus.wr.value = self._wr
        self.bus.rd.value = self._rd

    async def write(self, addr: int, dwr: bytes, byte_enable: int = None, sync: bool = True) -> None:
        """writes variable-lenght transaction to the write signals of the MI bus.

        Note:
            In reality, the transaction is divided into one or multiple 4B transactions.

        Args:
            addr: address, where the data are to be written to.
            dwr: data to be written to the dwr signal.
            byte_enable: optional, custom byte enable, if not set, all bytes are considered to be valid.
            sync: optional, True by default. If True, pause of one clock cycle is added after each 4B transaction.

        """

        cycles = ceildiv(self.data_width, len(dwr))

        for i in range(cycles):
            await self.write32(addr + i * self.data_width, dwr[i * self.data_width: (i + 1) * self.data_width], byte_enable, sync)

    async def write32(self, addr: int, dwr: bytes, byte_enable: int = None, sync: bool = True) -> None:
        """writes two 4B transaction to the write signals of the MI bus.

        Args:
            addr: address, where the data are to be written to.
            dwr: data to be written to the dwr signal.
            byte_enable: optional, custom byte enable, if not set, all bytes are considered to be valid.
            sync: optional, True by default. If True, pause of one clock cycle is added after the transaction.

        """

        await self._clk_re

        self._wr = 1
        self._addr = addr
        self._dwr = dwr

        if byte_enable is None:
            byte_enable = 2**len(dwr) - 1

        self._be = byte_enable

        self.log.debug(f"Writting {self._dwr.hex()} to {self._addr.to_bytes(self.addr_width, 'little').hex()} with byte_enable: {self._be}")

        self._propagate_control_signals()

        await await_signal_sync(self._clk_re, self.bus.ardy)

        self._clear_control_signals()
        self._propagate_control_signals()

        if sync:
            await self._clk_re

    async def write64(self, addr: int, dwr: bytes, byte_enable: int = None, sync: bool = True) -> None:
        """writes two 4B transaction to the write signals of the MI bus.

        Args:
            addr: address, where the data are to be written to.
            dwr: data to be written to the dwr signal.
            byte_enable: optional, custom byte enable, if not set, all bytes are considered to be valid.
            sync: optional, True by default. If True, pause of one clock cycle is added after each 4B transaction.

        """

        await self.write(addr, dwr, byte_enable, sync)

    async def read(self, addr: int, byte_count: bytes, byte_enable: int = None, sync: bool = True) -> bytes:
        """Reads variable-lenght transaction from the read signals of the MI bus.

        Note:
            In reality, the transaction is divided into one or multiple 4B transactions.

        Args:
            addr: address, where the data are to be written to.
            byte_count: number of bytes to be returned.
            sync: optional, True by default. If True, pause of one clock cycle is added after the transaction.

        Returns:
            Returns data of the requested length.

        """

        drd = bytearray(byte_count)

        cycles = ceildiv(self.data_width, byte_count)

        for i in range(cycles):
            drd[i * self.data_width: (i + 1) * self.data_width] = await self.read32(addr + i * self.data_width, byte_enable, sync)

        return bytes(drd[0: byte_count])

    async def read32(self, addr: int, byte_enable: int = None, sync: bool = True) -> bytes:
        """Reads one 4B transaction from the read signals of the MI bus.

        Args:
            addr: address, where the data are to be written to.
            sync: optional, True by default. If True, pause of one clock cycle is added after the transaction.

        Returns:
            Returns 4B of data.

        """

        drd = bytearray(self.data_width)

        await self._clk_re

        self._rd = 1
        self._addr = addr

        if byte_enable is None:
            byte_enable = 2**len(drd) - 1

        self._be = byte_enable

        self._propagate_control_signals()

        await await_signal_sync(self._clk_re, self.bus.ardy)

        self._clear_control_signals()
        self._propagate_control_signals()

        await await_signal_sync(self._clk_re, self.bus.drdy)

        rd_data = self.bus.drd.value
        rd_data.big_endian = False
        drd = rd_data.buff

        self.log.debug(f"Read {drd.hex()} from {addr.to_bytes(self.addr_width, 'little').hex()}")

        if sync:
            await self._clk_re

        return bytes(drd)

    async def read64(self, addr: int, byte_enable: int = None, sync: bool = True) -> bytes:
        """Reads two 4B transaction from the read signals of the MI bus.

        Args:
            addr: address, where the data are to be written to.
            sync: optional, True by default. If True, pause of one clock cycle is added after the transaction.

        Returns:
            Returns 8B of data.

        """

        drd = await self.read(addr, 8, byte_enable, sync)
        return bytes(drd)


class MISlaveDriver(BusDriver):
    """Slave driver intended for the MI BUS that allows sending data to the read signals of the bus.

    Atributes:
        _clk_re(cocotb.triggers.RisingEdge): object used for awaiting the rising edge of clock signal.
        addr_width(int): width of ADDR port in bytes.
        data_width(int): width of DATA port in bytes.
        _addr(int), _dwr(bytearray), _be(int), _wr(int), _rd(int): control signals that are then propagated to the MI BUS.

    """

    _signals = ["addr", "dwr", "be", "wr", "rd", "ardy", "drd", "drdy"]
    _optional_signals = ["mwr"]

    def __init__(self, entity, name, clock, array_idx=None) -> None:
        super().__init__(entity, name, clock, array_idx=array_idx)
        self.addr_width = len(self.bus.addr) // 8
        self.data_width = len(self.bus.dwr) // 8
        self._clear_control_signals()
        self._propagate_control_signals()

    def _clear_control_signals(self) -> None:
        """Sets control signals to default values without sending them to the MI bus."""

        self._ardy = 0
        self._drdy = 0
        self._drd = bytearray(self.data_width)

    def _propagate_control_signals(self) -> None:
        """Sends value of control signals to the MI bus."""

        self.bus.ardy.value = self._ardy
        self.bus.drdy.value = self._drdy
        self.bus.drd.value = int.from_bytes(self._drd, 'little')

    async def write(self, drd: bytes, sync: bool = True) -> None:
        """writes variable-lenght transaction to the read signals MI bus.

        Note:
            In reality, the transaction is divided into one or multiple 4B transactions.

        Args:
            drd: data to be written to the drd signal.
            sync: optional, True by default. If True, pause of one clock cycle is added after each 4B transaction.

        """

        cycles = ceildiv(self.data_width, len(drd))

        for i in range(cycles):
            await self.write32(drd[i * 4: i * 4 + 4], sync)

    async def write32(self, drd: bytes, sync: bool = True) -> None:
        """writes one 4B transaction to the read signals of the MI bus.

        Args:
            drd: data to be written to the drd signal.
            sync: optional, True by default. If True, pause of one clock cycle is added after the transaction.

        """

        await self._clk_re
        await await_signal_sync(self._clk_re, self.bus.rd)

        self._ardy = 1

        self._drd = drd
        self._drdy = 1

        self.log.debug(f"Responding with {self._drd.hex()} from {hex(self.bus.addr.value)}")

        self._propagate_control_signals()

        if sync:
            await self._clk_re
            self._clear_control_signals()
            self._propagate_control_signals()

    async def write64(self, drd: bytes, sync: bool = True) -> None:
        """writes two 4B transaction to the read signals of the MI bus.

        Args:
            drd: data to be written to the dwr signal.
            sync: optional, True by default. If True, pause of one clock cycle is added after each 4B transaction.

        """

        await self.write(drd, sync)
