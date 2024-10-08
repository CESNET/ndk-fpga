from cocotb_bus.monitors import BusMonitor
from cocotb.triggers import RisingEdge


class LBusMonitor(BusMonitor):
    _signals = ["data", "ena", "sop", "eop", "err", "mty"]
    _segments = 4

    def __init__(self, *args, packets=False, aux_signals=False,
                 data_type="buff", **kwargs):

        BusMonitor.__init__(self, *args, **kwargs)

    async def _monitor_recv(self):
        clk_redge = RisingEdge(self.clock)

        packet = None
        while True:
            await clk_redge

            for i in range(self._segments):
                if self.bus.ena.value.integer & (1 << i):
                    if self.bus.sop.value.integer & (1 << i):
                        assert packet is None
                        packet = []

                    data = self.bus.data[i].value.buff
                    if self.bus.eop.value.integer & (1 << i):
                        empty_count = self.bus.mty[i].value.integer
                        data = data[0:-empty_count] if empty_count else data

                    packet += data

                    if self.bus.eop.value.integer & (1 << i):
                        self._recv(packet)
                        packet = None
