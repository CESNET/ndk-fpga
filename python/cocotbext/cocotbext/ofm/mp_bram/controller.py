# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>


from cocotbext.ofm.base.drivers import BusDriver
from cocotbext.ofm.utils.math import ceildiv, bitmask
from cocotbext.ofm.utils.binary import Binary
from cocotbext.ofm.utils.signals import await_signal_sync


class MP_BRAM_Controller(BusDriver):
    _signals = ["WR_EN", "WR_ADDR", "WR_DATA", "RD_EN", "RD_ADDR", "RD_DATA_VLD", "RD_DATA"]
    _optional_signals = ["WR_BE", "RD_META_IN", "RD_META_OUT"]

    def __init__(self, entity, name, clock, array_idx=None, **kwargs):
        super().__init__(entity, name, clock, array_idx, **kwargs)

        self._write_ports = len(self.bus.WR_EN)
        self._read_ports  = len(self.bus.RD_EN)
        self._addr_width  = len(self.bus.WR_ADDR[0])
        self._data_width  = len(self.bus.WR_DATA[0])
        self._be_width    = len(self.bus.WR_BE[0])

        if self._be_width > 0:
            self._block_width = self._data_width // self._be_width
        else:
            self._block_width = 0

        self._clear_control_signals()

        for i in range(self._write_ports):
            self._propagate_write_signals(i)

        for i in range(self._read_ports):
            self._propagate_read_signals(i)

    def _clear_control_signals(self):
        self._wr_en   : int = 0
        self._wr_addr : int = 0
        self._wr_data : int = 0
        self._wr_be   : int = 0
        self._rd_en   : int = 0
        self._rd_addr : int = 0

    def _propagate_write_signals(self, port):
        self.bus.WR_EN[port].value   = self._wr_en
        self.bus.WR_ADDR[port].value = self._wr_addr
        self.bus.WR_DATA[port].value = self._wr_data
        self.bus.WR_BE[port].value   = self._wr_be

    def _propagate_read_signals(self, port):
        self.bus.RD_EN[port].value   = self._rd_en
        self.bus.RD_ADDR[port].value = self._rd_addr

    async def clear_memory(self):
        for i in range(2**self._addr_width):
            await self.write_word(address=i, data=0, port=0)

    async def write_word(self, address: int, data: int, port: int = 0, byte_enable: int | None = None, sync: bool = True) -> None:
        if sync:
            await self._clk_re

        self._wr_en   = 1
        self._wr_addr = address
        self._wr_data = data
        self._wr_be   = byte_enable if byte_enable is not None else bitmask(self._be_width)

        self.log.debug(f"write {hex(data)} to {address} at {port=}")

        self._propagate_write_signals(port)
        await self._clk_re

        self._clear_control_signals()
        self._propagate_write_signals(port)

    async def read_word(self, address: int, port: int = 0, sync: bool = True) -> int:
        if sync:
            await self._clk_re

        self._rd_en   = 1
        self._rd_addr = address

        self._propagate_read_signals(port)
        await self._clk_re

        self._rd_en = 0
        self._propagate_read_signals(port)

        await await_signal_sync(self._clk_re, self.bus.RD_DATA_VLD[0])

        data = self.bus.RD_DATA[0].value.integer

        self.log.debug(f"read {hex(data)} from {address} at {port=}.")

        self._clear_control_signals()
        self._propagate_read_signals(port)

        return data

    async def write(self, address: int, data: bytes, byte_enable: int | None = None, parallel: bool = True, sync: bool = True) -> None:
        if sync:
            await self._clk_re

        word_cnt = ceildiv(self._data_width, len(data) * 8)
        data_bin = Binary(data)
        port = 0
        data_staged = False

        if byte_enable is None:
            be_bin = Binary(bitmask(ceildiv(self._block_width, data_bin.bits))) if self._be_width > 0 else Binary(0)
        else:
            be_bin = Binary(byte_enable)

        for i in range(word_cnt):
            self._wr_en   = 1
            self._wr_addr = address
            self._wr_data = data_bin[i * self._data_width : (i + 1) * self._data_width].int
            self._wr_be   = be_bin[i * self._be_width : (i + 1) * self._be_width].int

            self.log.debug(f"write {hex(self._wr_data)} to {self._wr_addr} at {port=}")

            data_staged = True

            self._propagate_write_signals(port)

            address += 1

            if parallel:
                if port == self._write_ports - 1:
                    port = 0
                    data_staged = False
                    self._clear_control_signals()
                    await self._clk_re
                else:
                    port += 1
            else:
                await self._clk_re

        if data_staged:
            await self._clk_re

        self._clear_control_signals()

        for i in range(self._write_ports):
            self._propagate_write_signals(i)

    async def read(self, address: int, byte_count: int, parallel: bool = True, sync: bool = True) -> bytes:
        if sync:
            await self._clk_re

        offset_addr = address
        width = self._data_width
        word_cnt = ceildiv(width, byte_count*8)
        data_bin = Binary(bits=byte_count*8)
        send_checksum = 0
        recv_checksum = 0

        if parallel:
            port_offset = [0] * self._read_ports

            while recv_checksum < word_cnt:
                for port in range(self._read_ports):
                    if send_checksum < word_cnt:
                        self._rd_en   = 1
                        self._rd_addr = offset_addr

                        offset_addr += 1
                        send_checksum += 1

                    else:
                        self._rd_en   = 0
                        self._rd_addr = 0

                    if self.bus.RD_DATA_VLD[port].value:
                        offset = port + port_offset[port] * self._read_ports
                        data_bin[offset * width : (offset + 1) * width] = self.bus.RD_DATA[port].value.integer # pozor na endian!

                        self.log.debug(f"read {hex(data_bin[offset * width : (offset + 1) * width].int)} from {address + offset} at {port=}")

                        port_offset[port] += 1
                        recv_checksum += 1

                    self._propagate_read_signals(port)

                await self._clk_re

        else: # not parallel
            port = 0

            for i in range(word_cnt):
                self._rd_en   = 1
                self._rd_addr = offset_addr

                self._propagate_read_signals(port)
                offset_addr += 1

                await self._clk_re

                self._rd_en = 0
                self._propagate_read_signals(port)

                await await_signal_sync(self._clk_re, self.bus.RD_DATA_VLD[0])

                data_bin[i * width : (i + 1) * width] = self.bus.RD_DATA[0].value.integer

                self.log.debug(f"read {hex(data_bin[i * width : (i + 1) * width].int)} from {self._rd_addr} at port {port=}.")

        self._clear_control_signals()

        for i in range(self._read_ports):
            self._propagate_read_signals(i)

        return data_bin.bytes
