import copy

import cocotb
from cocotb.triggers import RisingEdge
from cocotb_bus.drivers import BusDriver


class Axi4StreamMaster(BusDriver):
    _signals = ["TVALID", "TREADY", "TDATA"]
    _optional_signals = ["TLAST", "TSTRB", "TKEEP", "TID", "TDEST", "TUSER"]

    def __init__(self, entity, name, clock, array_idx=None):
        BusDriver.__init__(self, entity, name, clock, array_idx=array_idx)

        ms, os = self._signals, self._optional_signals
        signals = ms | os if isinstance(ms, dict) else ms + os
        for s in signals:
            if hasattr(self.bus, s) and s not in ["TREADY"]:
                val = 2 ** getattr(self.bus, s).value.n_bits - 1 if s in ["TSTRB", "TKEEP"] else 0
                getattr(self.bus, s).setimmediatevalue(val)

    @cocotb.coroutine
    async def write(self, data, sync=True):
        data = copy.copy(data)

        if sync:
            await RisingEdge(self.clock)

        self.bus.TVALID.value = 1

        for signal, value in data.items():
            getattr(self.bus, signal).value = value

        await RisingEdge(self.clock)
        while hasattr(self.bus, "TREADY") and not self.bus.TREADY.value:
            await RisingEdge(self.clock)

        self.bus.TVALID.value = 0


class Axi4StreamSlave(BusDriver):
    _signals = ["TVALID", "TREADY"]

    def __init__(self, entity, name, clock, array_idx=None):
        BusDriver.__init__(self, entity, name, clock, array_idx=array_idx)

        self.bus.TREADY.setimmediatevalue(1)
