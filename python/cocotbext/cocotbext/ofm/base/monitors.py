# monitors.py: Fixed bus monitor for cocotb 2.0
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <ondrejschwarz@cesnet.cz>

import cocotb_bus.monitors as cbm
from .bus_fixup import do_fix, BusProxy


do_fix()


class BusMonitor(cbm.BusMonitor):
    def __init__(self, *args, **kwargs):
        array_idx = kwargs.pop("array_idx", None)
        super().__init__(*args, **kwargs)

        # replace bus with bus proxy
        self.bus = BusProxy(self.bus, array_idx)
