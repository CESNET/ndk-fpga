from typing import Optional, Union
import cocotb
import cocotb.triggers
import cocotb.utils

from .. import modelsim as ms

from cocotbext.ofm.mfb.monitors import MFBMonitor


st = cocotb.utils.get_sim_time


class Bus():
    _w = ms
    _SIGNALS = [] # or {}

    def __init__(self, instance, prefix: str, index: Optional[Union[list[int], int]] = None, label: Optional[str] = None, sep: str = '_', slices: Optional[int] = None):
        """
        slices: Meaningful only when index is specified.
                Specifies the number of separate buses in the one shared std_logic_vector,
                as the Bus class has to select the right slice.
                The bus configuration must be the same for all buses in that vector.
                For an n-dimensional bus signal, the value specifies the number of buses in the last dimension.
        """

        self._instance = instance
        self._prefix = prefix
        self._index = index
        self._slices = slices
        self._sep = sep
        self._label = label

    def _get_handle_slice(self, name):
        o = getattr(self._instance, self._prefix + self._sep + name)
        sl = ()
        if self._index is not None:
            if self._slices is not None:
                w = len(o) // self._slices
                sl = (self._index * w, (self._index + 1) * w)

            else:
                o = o[self._index]
        return o, sl

    def _get_handle(self, name):
        return self._get_handle_slice(name)[0]

    def add_wave(self, **kwargs):
        groups = self._get_groups(**kwargs)
        for s in self._SIGNALS:
            h, sl = self._get_handle_slice(s)
            p = self._w.cocotb2path(h, sl)
            self._w.add_wave(p, label=s, groups=groups)

    def _get_groups(self, **kwargs):
        groups = kwargs.get("groups", []).copy()
        if self._label is not None:
            groups.append(self._label)
        elif not groups:
            groups.append(self._prefix)
        return groups


class MvbBus(Bus):
    _SIGNALS = ['DATA', 'VLD', 'SRC_RDY', 'DST_RDY']
    _ITEMS = []

    def add_wave(self, **kwargs):
        super().add_wave(**kwargs)
        o = self._get_handle('DATA')
        sr = self._get_handle('SRC_RDY')
        dr = self._get_handle('DST_RDY')
        vld = self._get_handle('VLD')

        dw = len(o)
        off = dw // len(vld)
        for v in range(len(vld)):
            groups = self._get_groups(**kwargs)
            groups.append(v)
            ho = self._w.cmd(f"virtual function {{{self._w.cocotb2path(sr)} and {self._w.cocotb2path(dr)} and {self._w.cocotb2path(vld[v])}}} handover")
            self._w.add_wave(ho, groups=groups, label='handover')
            for name, ran in self._ITEMS:
                bus = [(o, range(ran.start + off * v, ran.stop + off * v))]
                self._w.add_wave(f"{name}", groups=groups, bus=bus)


class MfbBus(Bus):
    _SIGNALS = ['DATA', 'SRC_RDY', 'DST_RDY', 'SOF', 'EOF', 'SOF_POS', 'EOF_POS']

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.clear()

    def add_wave(self, **kwargs):
        super().add_wave(**kwargs)

        groups = self._get_groups(**kwargs)
        sr, srs = self._get_handle_slice('SRC_RDY')
        dr, drs = self._get_handle_slice('DST_RDY')

        name = self._w.cmd(f"virtual function {{{self._w.cocotb2path(sr, srs)} and {self._w.cocotb2path(dr, drs)}}} transfer")
        self._w.add_wave(name, groups=groups, label='transfer')

    def clear(self):
        self._sum_pkts = 0
        self._sum_cycles = 0
        self._sum_bytes = 0

    async def monitor(self, clk):
        self.clear()

        m = MFBMonitor(self._instance, self._prefix, clk, array_idx=self._index)

        def cb_transaction(trn):
            self._sum_pkts += 1
            self._sum_bytes += len(trn)

        m.add_callback(cb_transaction)

        tpre = st()
        while True:
            tpost = st()
            tdiff = (tpost - tpre) / 1000  # to Mpps

            self._sum_cycles += 1
            sc = self._sum_cycles
            if sc > 0 and tdiff > 0:
                self._thr = float(self._sum_bytes) * 8 / float(sc * tdiff)

            tpre = tpost


class MiBus(Bus):
    _SIGNALS = ['ADDR', 'DWR', 'BE', 'RD', 'WR', 'DRD', 'ARDY', 'DRDY']


class DmaUpMvbBus(MvbBus):
    _ITEMS = [
        ('length',     range(0,  11)),
        ('type',       range(11, 12)),
        ('firstib',    range(12, 14)),
        ('lastib',     range(14, 16)),
        ('tag',        range(16, 24)),
        ('unitid',     range(24, 32)),
        ('global',     range(32, 96)),
        ('relaxed',    range(96, 97)),
    ]


class DmaDownMvbBus(MvbBus):
    _ITEMS = [
        ('length',     range(0,  11)),
        ('completed',  range(11, 12)),
        ('tag',        range(12, 20)),
        ('unitid',     range(20, 28)),
    ]
