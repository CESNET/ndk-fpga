# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>

from cocotbext.ofm.base.transaction import IdleTransaction
from cocotbext.ofm.base.drivers import ModularBusDriver
from cocotbext.ofm.mvb.drivers import MVBDriver
from cocotbext.ofm.mfb.drivers import MFBDriver
from cocotbext.ofm.mfb.transaction import MfbTransaction
from protocol import PcieMvbProtocol


class PcieDriver(ModularBusDriver):
    def __init__(self, entity, name, clock, array_idx=None):
        super().__init__(entity, name, clock, array_idx=array_idx)
        self.mfb_drv = MFBDriver(entity, name+"_MFB", clock, array_idx=array_idx, no_inner_idles=True, generics_prefix="PCIE_DOWN")
        self.mvb_drv = MVBDriver(entity, name+"_MVB", clock, array_idx=array_idx, protocol=PcieMvbProtocol)

    def append(self, transaction):
        hdr, data = transaction

        if self.mfb_drv.frame_cnt == 0:
            pass

        self.mfb_drv.append(MfbTransaction(data=data))
        self.mvb_drv.append(hdr)

    async def _split_transaction(self, transaction):
        if isinstance(transaction, IdleTransaction):
            await self._clk_re
            return
        yield
