# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2023-2026 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#            Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from typing import Optional, Union
import logging
import cocotb
import cocotb.triggers
import cocotb.utils

from cocotb.types import Array

from .. import modelsim as ms

from cocotbext.ofm.mfb.monitors import MFBMonitor
from cocotbext.ofm.base.bus_fixup import SignalProxy


st = cocotb.utils.get_sim_time
logger = logging.getLogger(__name__)


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
        attr = self._prefix + self._sep + name
        if not hasattr(self._instance, attr):
            return None, None

        o = getattr(self._instance, attr)
        sl = ()
        if self._index is not None:
            if self._slices is not None:
                w = len(o) // self._slices
                sl = (self._index * w, (self._index + 1) * w)

            else:
                o = SignalProxy(o, self._index)

        else:
            o = SignalProxy(o, self._index)

        return o, sl

    def _get_handle(self, name):
        return self._get_handle_slice(name)[0]

    def _get_handle_span(self, name):
        """Returns (handle, low, width) of this bus' part of the signal: the
        whole signal, or its slice when the bus shares it with others."""
        h, sl = self._get_handle_slice(name)
        if h is None:
            return None, 0, 0
        if sl:
            return h, sl[0], sl[1] - sl[0]
        return h, 0, len(h)

    def add_wave(self, **kwargs):
        """Adds every signal of _SIGNALS the design has."""
        groups = self._get_groups(**kwargs)
        found = False
        for s in self._SIGNALS:
            h, sl = self._get_handle_slice(s)
            if h is not None:
                found = True
                p = self._w.cocotb2path(h, sl)
                self._w.add_wave(p, **(kwargs | dict(groups=groups, label=s)))

        if not found:
            path = getattr(self._instance, '_path', self._instance)
            raise AttributeError(f"{type(self).__name__}: no signal of bus '{self._prefix}' found in {path}, expected some of {self._SIGNALS}")

    def _add_transfer(self, terms, item=None, **kwargs):
        """Adds a "transfer" virtual function, high while all present terms
        are. Terms are (handle, slice) pairs, a None handle is left out."""
        terms = [t for t in terms if t[0] is not None]
        if not terms:
            return

        parts = [self._prefix, 'transfer']
        if self._index is not None:
            parts += [str(i) for i in (self._index if isinstance(self._index, list) else [self._index])]
        if item is not None:
            parts.append(str(item))

        expr = " and ".join(self._w.cocotb2path(h, sl) for h, sl in terms)
        name = self._w.cmd(f"virtual function {{{expr}}} {'__'.join(parts)}")
        self._w.add_wave(name, **(kwargs | dict(label='transfer', color='yellow')))

    def _get_groups(self, **kwargs):
        groups = kwargs.get("groups", []).copy()
        if self._label is not None:
            groups.append(self._label)
        elif not groups:
            groups.append(self._prefix)
        return groups


class MvbBus(Bus):
    # Control signals; DATA, or any other signal a subclass lists in _SIGNALS,
    # is split per item. A bus with differently named data signals can use:
    #   _SIGNALS = ['ADDR', 'LEN'] + MvbBus._BASE_SIGNALS
    _BASE_SIGNALS = ['VLD', 'SRC_RDY', 'DST_RDY']
    _SIGNALS = ['DATA'] + _BASE_SIGNALS
    _ITEMS = []

    def add_wave(self, **kwargs):
        # VLD defines the item dimension, one bit per item. An array of
        # vectors means an array of buses, whose index must be given.
        vld = self._get_handle('VLD')
        if vld is not None and isinstance(vld.value, Array):
            raise ValueError(f"{type(self).__name__}: {self._prefix}{self._sep}VLD is an array of buses, pass the bus index")

        super().add_wave(**kwargs)
        groups = self._get_groups(**kwargs)
        sr = self._get_handle_slice('SRC_RDY')
        dr = self._get_handle_slice('DST_RDY')
        vld, vld_l, vld_w = self._get_handle_span('VLD')
        items = 1 if vld is None else vld_w

        # A signal is split per item only when its width divides evenly;
        # anything else (e.g. a flag shared by all items) is shown just as
        # a whole, by Bus.add_wave above.
        def item_span(name):
            h, low, width = self._get_handle_span(name)
            if h is None or width % items != 0:
                if h is not None and items > 1:
                    logger.info(f"{self._prefix}_{name}: width {width} is not a multiple of {items} items, not split per item")
                return None
            return h, low, width // items

        split = [(name, None) for name in self._SIGNALS if name not in ['DATA'] + self._BASE_SIGNALS]
        if self._ITEMS:
            split += [('DATA', self._ITEMS)]

        spans = []
        for name, fields in split:
            span = item_span(name)
            if span is not None:
                spans.append((name, fields, *span))

        for v in range(items):
            igroups = groups + [v]
            if vld is None:
                vld_term = (None, ())
            elif self._slices is not None:
                vld_term = (vld, (vld_l + v,))
            else:
                vld_term = (vld[v], ())
            self._add_transfer([sr, dr, vld_term], item=v if items > 1 else None, **(kwargs | dict(groups=igroups)))

            for name, fields, h, low, w in spans:
                off = low + w * v
                for label, ran in (fields or [(name, range(0, w))]):
                    bus = [(h, range(ran.start + off, ran.stop + off))]
                    self._w.add_wave(f"{label}", **(kwargs | dict(groups=igroups, bus=bus)))


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

        self._add_transfer([(sr, srs), (dr, drs)], **(kwargs | dict(groups=groups)))

    def clear(self):
        self._sum_pkts = 0
        self._sum_cycles = 0
        self._sum_bytes = 0

    async def monitor(self, clk):
        re = cocotb.triggers.RisingEdge(clk)

        self.clear()

        m = MFBMonitor(self._instance, self._prefix, clk, array_idx=self._index)

        def cb_transaction(trn):
            self._sum_pkts += 1
            self._sum_bytes += len(trn)

        m.add_callback(cb_transaction)

        tpre = st()
        while True:
            await re

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
