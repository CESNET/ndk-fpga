from cocotb_bus.monitors import BusMonitor
from cocotb.triggers import RisingEdge


class AvstPcieMonitor(BusMonitor):
    _signals = ["DATA", "HDR", "SOP", "EOP", "VALID", "READY"]
    _optional_signals = ["ERROR", "PREFIX"]

    def __init__(self, *args, aux_signals=False, **kwargs):
        BusMonitor.__init__(self, *args, **kwargs)

        self._segments = len(self.bus.VALID)
        self._segment_width = len(self.bus.DATA) // self._segments

        self._transaction = bytearray(0)
        self._header = bytearray(0)

        self.aux_signals = aux_signals

        ms = AvstPcieMonitor._signals if isinstance(AvstPcieMonitor._signals, dict) else {s: s for s in self._signals}
        os = AvstPcieMonitor._optional_signals if isinstance(AvstPcieMonitor._optional_signals, dict) else {
            s: s for s in self._optional_signals}
        os_filt = {k: s for k, s in os.items() if hasattr(self.bus, s)}

        self._recv_signals = ms | os_filt

    async def _monitor_recv(self):
        re = RisingEdge(self.clock)

        while True:
            await re

            if self.bus.READY.value == 1:
                for i in range(self._segments):
                    segment = {}
                    for k, s in self._recv_signals.items():
                        if s not in ["READY"]:
                            signal = getattr(self.bus, s).value.buff
                            # TODO: try to use slicing instead of shifting (at least for data and headers)
                            signal = int.from_bytes(signal, byteorder="big")
                            signal = signal >> i * max(len(getattr(self.bus, s)) // self._segments, 1)
                            sig_len = len(getattr(self.bus, s))
                            mask = 2**int(sig_len / self._segments) - 1
                            signal = signal & mask
                            if s in ["DATA", "HDR"]:
                                signal = signal.to_bytes(int(sig_len / self._segments), byteorder="big")
                            segment[k] = signal

                    if segment["VALID"] == 1:
                        # Append bytes in reverse order from the last to the self._segment_width//8-1 from the end
                        # The amount of appended bytes = segment width in bytes
                        self._transaction += segment["DATA"][-1:-self._segment_width // 8 - 1:-1]
                        if segment["SOP"] == 1:
                            self._header = segment["HDR"]
                        if segment["EOP"] == 1:
                            self._recv((self._header, self._transaction))
                            self._transaction = bytearray(0)
                            self._header = bytearray(0)
