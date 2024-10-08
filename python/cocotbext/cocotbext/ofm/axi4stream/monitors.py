import cocotb
from cocotb_bus.monitors import BusMonitor
from cocotb.triggers import RisingEdge


class Axi4Stream(BusMonitor):
    _signals = ["TVALID", "TREADY"]
    _optional_signals = ["TDATA", "TLAST", "TSTRB", "TKEEP", "TID", "TDEST", "TUSER"]

    _optional_data_signals = \
        tuple(signal for signal in _optional_signals if signal != "TREADY")

    def __init__(self, *args, aux_signals=False, **kwargs):
        BusMonitor.__init__(self, *args, **kwargs)

        self.aux_signals = aux_signals

        os = Axi4Stream._optional_signals if isinstance(Axi4Stream._optional_signals, dict) else {s: s for s in self._optional_signals}
        self._recv_signals = {k: s for k, s in os.items() if hasattr(self.bus, s)}

    @cocotb.coroutine
    async def _monitor_recv(self):
        re = RisingEdge(self.clock)

        while True:
            await re

            if self.bus.TVALID.value and self.bus.TREADY.value:
                word = {k: getattr(self.bus, s).value.buff for k, s in self._recv_signals.items()}
                self._recv(word)
