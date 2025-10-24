from .. import modelsim as ms


class Bus():
    _w = ms
    _SIGNALS = [] # or {}

    def __init__(self, instance, prefix, index=None, label=None, sep='_'):
        self._instance = instance
        self._prefix = prefix
        self._index = index
        self._sep = sep
        self._label = label if label is not None else prefix

    def _get_handle(self, name):
        o = getattr(self._instance, self._prefix + self._sep + name)
        if self._index is not None:
            o = o[self._index]
        return o

    def add_wave(self, **kwargs):
        os = []
        for s in self._SIGNALS:
            os.append(self._get_handle(s))
        self._w.add_wave(*os, group=self._label) # , expand=self._prefix)


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
            groups = [self._label, v]
            ho = self._w.cmd(f"virtual function {{{self._w.cocotb2path(sr)} and {self._w.cocotb2path(dr)} and {self._w.cocotb2path(vld[v])}}} handover")
            self._w.add_wave(ho, groups=groups, label='handover')
            for name, ran in self._ITEMS:
                bus = [(o, range(ran.start + off * v, ran.stop + off * v))]
                self._w.add_wave(f"{name}", groups=groups, bus=bus)


class MfbBus(Bus):
    _SIGNALS = ['DATA', 'SRC_RDY', 'DST_RDY', 'SOF', 'EOF', 'SOF_POS', 'EOF_POS']


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
