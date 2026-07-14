# monitors.py: Fixed bus monitor for cocotb 2.0
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <ondrejschwarz@cesnet.cz>

import cocotb
import cocotb_bus.monitors as cbm
from .bus_fixup import do_fix


do_fix()


if cocotb.__version__ >= "2.0.0":
    from .bus_fixup import BusProxy

    class BusMonitor(cbm.BusMonitor):
        def __init__(self, *args, **kwargs):
            array_idx = kwargs.pop("array_idx", None)
            super().__init__(*args, **kwargs)

            # replace bus with bus proxy
            self.bus = BusProxy(self.bus, array_idx)

else:
    BusMonitor = cbm.BusMonitor
