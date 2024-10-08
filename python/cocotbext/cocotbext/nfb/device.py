import os
import lzma
import libfdt
import fdt

import nfb

from ..ofm.utils import RAM
from .queue import QueueManager

from .ext.python import Servicer as NfbPythonServicer

import cocotb

e = cocotb.external


class NfbDevice:
    def __init__(self, dut, ram=None, servicer=NfbPythonServicer):
        self.dtb = None
        self.dma = None
        self.mi = None
        self._dut = dut

        self.ram = ram if ram else RAM(0x02000000)
        self._servicer_cls = servicer

        self._init_pcie()

    async def init(self):
        await self._init_clks()
        await self._reset()

        self.dtb = self.read_dtb()
        self._fdt = libfdt.Fdt(self.dtb)
        self.fdt = fdt.parse_dtb(self.dtb)

        self._servicer = self._servicer_cls(self, dtb=self.dtb)

        self.nfb = await e(nfb.open)(self._servicer.path())

        self.dma = QueueManager(self)

    async def _init_clks(self):
        pass

    def _init_pcie(self):
        pass

    async def _reset(self):
        pass

    def read_dtb(self):
        with open(os.environ["NETCOPE_TEMP"] + "DevTree.dtb", "rb") as f:
            return f.read()

    async def read_dtb_raw(self):
        data = await self._read_dtb_raw()
        return lzma.LZMADecompressor(format=lzma.FORMAT_XZ).decompress(data)

    async def test_dtb(self):
        assert self.dtb == await self.read_dtb_raw()
