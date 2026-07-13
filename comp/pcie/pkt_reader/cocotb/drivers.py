# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>

from random import randint

from cocotb.triggers import ClockCycles

from cocotbext.ofm.base.drivers import BusDriver
from cocotbext.ofm.mvb.drivers import MVBDriver
from cocotbext.ofm.mfb.drivers import MFBDriver
from cocotbext.ofm.mfb.transaction import MfbTransaction


class PprDriver(MVBDriver):
    _optional_signals = ["id", "address", "length"]


class PcieDriver(BusDriver):
    _signals = ["data", "sof", "eof", "sof_pos", "eof_pos"]

    def __init__(self, entity, name, clock, array_idx=None):
        super().__init__(entity, name, clock, array_idx=array_idx)
        self.mfb_drv = MFBDriver(entity, name+"_MFB", clock, array_idx=array_idx)
        self.mvb_drv = MVBDriver(entity, name+"_MVB", clock, array_idx=array_idx)

    async def _driver_send(self, transaction, sync=True, **kwargs) -> None:
        """Distributes the data and header to the respective interface drivers."""
        hdr, data = transaction
        if self.mfb_drv.frame_cnt == 0:
            await ClockCycles(self.clock, 5)
        await ClockCycles(self.clock, randint(0, 10))
        # TODO: Idle generators
        self.mfb_drv.append(MfbTransaction(data=data))
        self.mvb_drv.append(hdr)
