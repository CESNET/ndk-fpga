# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>

import sys

from dataclasses import dataclass, field, fields
from ..base.transaction import Transaction
from ..utils import concat, deconcat


@dataclass
class MvbTransaction(Transaction):
    """Base class for MVB Transactions with configurable data items"""

    @classmethod
    def from_bytes(cls, tr: bytes):
        """Class method for compatibility with versions when MVB driver accepted only bytes.
           Returns a MvbTransaction object.
        """

        mvb_tr = MvbTrClassic()
        mvb_tr.data = int.from_bytes(tr, byteorder=sys.byteorder)
        return mvb_tr


@dataclass
class MvbTrClassic(MvbTransaction):
    data : int = 0


@dataclass
class MvbTrClassicWithMeta(MvbTransaction):
    data : int = 0
    meta : int = 0


@dataclass
class MvbTrAddressWithMeta(MvbTransaction):
    addr : int = 0
    meta : int = 0

#  Please do not add any more Transaction types here.
#  They belong in transaction.py of the specific test that needs them.


def hdrfield(width: int, repr=repr, /, **kwargs):
    """Create a dataclass field with width metadata for serialization.

    Args:
        width: Bit width of the field
        repr: Format function for the field in __repr__ (default: built-in repr)

    Returns:
        A dataclass.field with metadata containing 'width' and 'repr' keys.
    """
    return field(metadata={'width': width, 'repr': repr}, default=0, **kwargs)


def serializableheader():
    """Decorator for SerializableHeader subclasses. Disables auto-__repr__.

    Uses kw_only=True to prevent positional argument issues and ensure
    fields are initialized correctly from keyword arguments only.
    """
    return dataclass(repr=False, kw_only=True)


@serializableheader()
class MvbTrClassicSerializable(MvbTrClassic):
    """MvbTrClassic class providing serialize/deserialize for bitfield structures.

    Subclasses define fields using hdrfield().
    Example - MVB transaction data signal contains multiple fields:

        @serializableheader()
        class MyMvbTr(MvbTrClassicSerializable):
            addr:   int = hdrfield(16)
            length: int = hdrfield(16)

        tr = MyMvbTr(data=1234)
        print(tr)  # MyMvbTr(addr=4660, length=43981)
    """

    def _hdr_fields(self):
        """Return hdrfield dataclass fields (with 'width' metadata, excluding packed_field)."""
        return [f for f in fields(self) if 'width' in f.metadata]

    def _unpack(self, packed_val):
        """Deserialize a packed integer into individual hdrfields using deconcat()."""
        widths = [f.metadata['width'] for f in self._hdr_fields()]
        values = deconcat([packed_val] + widths)
        for f, val in zip(self._hdr_fields(), values):
            setattr(self, f.name, val)

    def serialize(self):
        """Pack all hdrfields into a single integer using concat()."""
        vwpairs = [(getattr(self, f.name), f.metadata['width'])
                   for f in fields(self) if 'width' in f.metadata]
        return concat(vwpairs)

    def __repr__(self):
        flds = self._hdr_fields()
        if not flds:
            return f"{self.__class__.__qualname__}()"
        return (
            f"{self.__class__.__qualname__}(" +
            ', '.join([f"{f.name}={f.metadata['repr'](getattr(self, f.name))}" for f in flds]) +
            ')'
        )

    def __len__(self):
        """Return total bit width of all hdrfields."""
        return sum(f.metadata['width'] for f in self._hdr_fields())

    @classmethod
    def deserialize(cls, val: int):
        """Create instance from a packed integer.

        If packed_field is set, also stores the value there and syncs fields.
        Otherwise, sets individual hdrfields directly.
        """
        obj = cls()
        obj._unpack(val)
        return obj
