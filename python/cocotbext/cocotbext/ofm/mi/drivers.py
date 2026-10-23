# drivers.py: MI Drivers
# Copyright (C) 2024-2026 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

from cocotbext.ofm.base.drivers import BusDriver
from cocotbext.ofm.utils.math import ceildiv
from cocotbext.ofm.utils.signals import await_signal_sync, align_write_request, align_read_request
from cocotbext.ofm.mi.transaction import MiTransactionType
from cocotb.types import LogicArray, Logic
from typing import Optional


class MIRequestDriver(BusDriver):
    """Request driver intended for the MI BUS that allows sending data to and receiving from the bus."""

    _signals = ["addr", "dwr", "be", "wr", "rd", "ardy", "drd", "drdy"]
    _optional_signals = ["mwr"]

    def __init__(self, entity, name, clock, array_idx=None) -> None:
        super().__init__(entity, name, clock, array_idx=array_idx)
        self.__addr_width = len(self.bus.addr) // 8
        self.__data_width = len(self.bus.dwr) // 8
        self._clear_control_signals()
        self._propagate_control_signals()

    @property
    def addr_width(self):
        return self.__addr_width

    @property
    def data_width(self):
        return self.__data_width

    def _clear_control_signals(self) -> None:
        """Sets control signals to default values without sending them to the MI bus."""

        self.__addr = LogicArray(0, len(self.bus.addr))
        self.__dwr = LogicArray(0, len(self.bus.dwr))
        self.__be = LogicArray(0, len(self.bus.be))
        self.__wr = Logic("0")
        self.__rd = Logic("0")

    def _propagate_control_signals(self) -> None:
        """Sends value of control signals to the MI bus."""
        self.bus.addr.value = self.__addr
        self.bus.dwr.value = self.__dwr
        self.bus.be.value = self.__be
        self.bus.wr.value = self.__wr
        self.bus.rd.value = self.__rd

    async def _write_word(self, addr: int, dwr: bytes, byte_enable: Optional[int] = None) -> None:
        """writes two 4B transaction to the write signals of the MI bus.

        Args:
            addr: address, where the data are to be written to.
            dwr: data to be written to the dwr signal.
            byte_enable: optional, custom byte enable, if not set, all bytes are considered to be valid.

        """
        assert addr >= 0

        await self._clk_re

        self.__wr = 1
        self.__addr[:] = addr
        self.__dwr = LogicArray.from_bytes(dwr, byteorder='little')

        if byte_enable is None:
            self.__be[:] = LogicArray.from_unsigned(2**self.__data_width - 1, self.__data_width)
        else:
            self.__be[:] = byte_enable

        self.log.debug(f"Writting {hex(self.__dwr)} to {hex(self.__addr)} with byte_enable: {bin(self.__be)}")

        self._propagate_control_signals()

        await await_signal_sync(self._clk_re, self.bus.ardy)

        self._clear_control_signals()
        self._propagate_control_signals()

    async def _read_word(self, addr: int, byte_enable: Optional[int] = None) -> bytes:
        """Reads one 4B transaction from the read signals of the MI bus.

        Args:
            addr: address, where the data are to be written to.

        Returns:
            Returns 4B of data.

        """
        assert addr >= 0

        await self._clk_re

        self.__rd = 1
        self.__addr[:] = addr

        if byte_enable is None:
            self.__be[:] = LogicArray.from_unsigned(2**self.__data_width - 1, self.__data_width)
        else:
            self.__be[:] = byte_enable

        self._propagate_control_signals()

        await await_signal_sync(self._clk_re, self.bus.ardy)

        self._clear_control_signals()
        self._propagate_control_signals()

        await await_signal_sync(self._clk_re, self.bus.drdy)

        drd = self.bus.drd.value.to_bytes(byteorder='little')

        self.log.debug(f"Read {drd.hex()} from {hex(addr)}")

        return drd

    async def write(self, addr: int, dwr: bytes, *, byte_enable: Optional[int] = None, bus_opts=None) -> None:
        """writes variable-lenght transaction to the write signals of the MI bus.

        Note:
            In reality, the transaction is divided into one or multiple 4B transactions.

        Args:
            addr: address to which the data are to be written.
            dwr: data to be written to the dwr signal.
            byte_enable: optional, custom byte enable, if not set, all bytes are considered to be valid.

        """
        assert addr >= 0

        be = LogicArray(2**len(dwr) - 1 if byte_enable is None else byte_enable, len(dwr))
        _, _, addr, dwr, be = align_write_request(self.__data_width, addr, dwr, byte_enable=be)

        cycles = ceildiv(self.__data_width, len(dwr))

        for i in range(cycles):
            be_slice = be[(i+1)*self.__data_width - 1 : i*self.__data_width]
            await self._write_word(addr + i*self.__data_width, dwr[i*self.__data_width : (i+1)*self.__data_width], be_slice.to_unsigned())

    async def read(self, addr: int, byte_count: int, byte_enable: Optional[int] = None, bus_opts=None) -> bytes:
        """Reads variable-lenght transaction from the read signals of the MI bus.

        Note:
            In reality, the transaction is divided into one or multiple 4B transactions.

        Args:
            addr: address, where the data are to be written to.
            byte_count: number of bytes to be returned.

        Returns:
            Returns data of the requested length.

        """
        assert addr >= 0

        be = LogicArray(2**byte_count - 1 if byte_enable is None else byte_enable, byte_count)
        start_offset, end_offset, addr, byte_count, be = align_read_request(self.__data_width, addr, byte_count, byte_enable=be)

        drd = bytearray(byte_count)

        cycles = ceildiv(self.__data_width, byte_count)

        for i in range(cycles):
            be_slice = be[(i+1)*self.__data_width - 1 : i*self.__data_width]
            drd[i*self.__data_width: (i+1)*self.__data_width] = await self._read_word(addr + i*self.__data_width, be_slice.to_unsigned())

        return bytes(drd[start_offset: byte_count-end_offset])

    async def read32(self, addr: int, byte_enable: Optional[int] = None) -> int:
        return int.from_bytes(await self.read(addr, byte_count=4, byte_enable=byte_enable), 'little')

    async def read64(self, addr: int, byte_enable: Optional[int] = None) -> int:
        return int.from_bytes(await self.read(addr, byte_count=8, byte_enable=byte_enable), 'little')


class MIResponseDriver(BusDriver):
    """Response driver intended for the MI BUS that allows sending data to the read signals of the bus.

    Atributes:
        _clk_re(cocotb.triggers.RisingEdge): object used for awaiting the rising edge of clock signal.
        __addr_width(int): width of ADDR port in bytes.
        __data_width(int): width of DATA port in bytes.
        __addr(int), __dwr(bytearray), __be(int), __wr(int), __rd(int): control signals that are then propagated to the MI BUS.

    """

    _signals = ["addr", "dwr", "be", "wr", "rd", "ardy", "drd", "drdy"]
    _optional_signals = ["mwr"]

    def __init__(self, entity, name, clock, array_idx=None) -> None:
        super().__init__(entity, name, clock, array_idx=array_idx)
        self.__addr_width = len(self.bus.addr) // 8
        self.__data_width = len(self.bus.dwr) // 8
        self._clear_control_signals()
        self._propagate_control_signals()

    def _clear_control_signals(self) -> None:
        """Sets control signals to default values without sending them to the MI bus."""

        self.__drdy = Logic("0")
        self.__drd = LogicArray(0, len(self.bus.drd))

    def _propagate_control_signals(self) -> None:
        """Sends value of control signals to the MI bus."""

        self.bus.drdy.value = self.__drdy
        self.bus.drd.value = self.__drd

    async def _write_word(self, drd: bytes) -> None:
        """writes one 4B transaction to the read signals of the MI bus.

        Args:
            drd: data to be written to the drd signal.

        """

        while not (self.bus.ardy.value and self.bus.rd.value):
            await self._clk_re

        self.__drd[:] = LogicArray.from_bytes(drd, byteorder='little')
        self.__drdy = 1

        self.log.debug(f"Responding with {hex(self.__drd)} from {hex(self.bus.addr.value)}")

        self._propagate_control_signals()

        await self._clk_re
        self._clear_control_signals()
        self._propagate_control_signals()

    async def write(self, drd: bytes) -> None:
        """writes variable-lenght transaction to the read signals MI bus.

        Note:
            In reality, the transaction is divided into one or multiple 4B transactions.

        Args:
            drd: data to be written to the drd signal.

        """

        cycles = ceildiv(self.__data_width, len(drd))

        for i in range(cycles):
            await self._write_word(drd[i * self.__data_width: (i+1) * self.__data_width])


class MIRequestDriverAgent(MIRequestDriver):
    """MI Request Driver with _send_thread function."""

    def __init__(self, entity, name, clock, array_idx=None) -> None:
        super().__init__(entity, name, clock, array_idx=array_idx)

    async def _send_thread(self) -> None:
        while True:
            while not self._sendQ:
                self._pending.clear()
                await self._pending.wait()

            while self._sendQ:
                transaction, callback, event, kwargs = self._sendQ.popleft()

                if transaction.trans_type == MiTransactionType.Request:  # read test
                    await self.read(transaction.addr, transaction.data_len)
                else:  # write test
                    await self.write(transaction.addr, transaction.data)

                if event:
                    event.set()
                if callback:
                    callback(transaction)


class MIResponseDriverAgent(MIResponseDriver):
    """MI Response Driver with _send_thread function."""

    def __init__(self, entity, name, clock, array_idx=None):
        super().__init__(entity, name, clock, array_idx=array_idx)

    async def _send_thread(self) -> None:
        while True:
            while not self._sendQ:
                self._pending.clear()
                await self._pending.wait()

            while self._sendQ:
                transaction, callback, event, kwargs = self._sendQ.popleft()

                if transaction.trans_type == MiTransactionType.Request:  # read test
                    await self.write(transaction.data)
                else:  # write test
                    pass

                if event:
                    event.set()
                if callback:
                    callback(transaction)
