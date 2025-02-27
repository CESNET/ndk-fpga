import sys

from dataclasses import dataclass
from ..base.transaction import Transaction


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
