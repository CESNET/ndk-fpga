from cocotb_bus.monitors import BusMonitor
from cocotb.triggers import RisingEdge


class AvstEthMonitor(BusMonitor):
    _signals = ["data", "valid", "sop", "eop", "ready", "empty"]
    # _optional_signals = ["err", "pause", "pfc", "skip_crc"]

    def __init__(self, *args, packets=False, aux_signals=False,
                 data_type="buff", **kwargs):

        BusMonitor.__init__(self, *args, **kwargs)

    async def _monitor_recv(self):
        re = RisingEdge(self.clock)

        packet = None
        while True:
            await re

            if self.bus.valid.value and self.bus.ready.value:
                if self.bus.sop.value:
                    assert packet is None
                    packet = []

                data = self.bus.data.value.buff
                if self.bus.eop.value:
                    empty_count = self.bus.empty.value.integer
                    data = data[0:-empty_count] if empty_count else data # endianity? This looks suspicious and is untested
                    # data = data[-1:-empty_count:-1] # This might work - byte reverse is included

                packet += data

                if self.bus.eop.value:
                    self._recv(packet)
                    packet = None
