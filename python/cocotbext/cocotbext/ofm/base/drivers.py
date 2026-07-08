# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2024-2026 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#            Ondřej Schwarz <ondrejschwarz@cesnet.cz>

import cocotb
import cocotb.utils
import cocotb_bus.drivers as cbd
from cocotb.triggers import RisingEdge

from .bus_fixup import do_fix
from .transaction import IdleTransaction
from .generators import IdleGenerator


do_fix()


class BusDriver(cbd.BusDriver):
    """
    BusDriver adds common functionality like

     * RisingEdge clock event (self._clk_re)
     * Configuration (self._cfg) can be used for example to configure specific idle generator
     * Idle generator (default is IdleGenerator, which doesn't generates any idles)
    """

    def __init__(self, entity, name, clock, array_idx=None, **kwargs):
        self._clk_re = RisingEdge(clock)

        self._cfg = dict(
            clk_freq=kwargs.get("clk_freq"),
        )

        self._idle_gen = IdleGenerator()
        self._idle_tr = IdleTransaction()

        # cocotb 2.0-only defines
        if cocotb.__version__ >= "2.0.0":
            from .bus_fixup import BusProxy

            # initiate without using array idx, which causes problems in cocotb 2.0
            super().__init__(entity, name, clock, array_idx=None)

            # replace bus with bus proxy
            self.bus = BusProxy(self.bus, array_idx)

        else:
            super().__init__(entity, name, clock, array_idx=array_idx)

        self._cfg_update()

    def _cfg_update(self, **kwargs):
        self._cfg.update(kwargs)

        self._idle_gen.configure(**self._cfg)

    def set_idle_generator(self, generator):
        self._idle_gen = generator
        self._cfg_update()

    async def _measure_clkfreq(self, trigger=None):
        """
        Measure the clock frequency by passing the simulation time

        This can simplify the configuration of some idle generators.
        """

        if trigger is None:
            trigger = self._clk_re

        t1 = cocotb.utils.get_sim_time('ps')
        await trigger
        t2 = cocotb.utils.get_sim_time('ps')

        clk_freq = 1e12 / (t2 - t1)
        self._cfg_update(clk_freq=clk_freq)
        return clk_freq
