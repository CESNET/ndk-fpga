# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from dataclasses import dataclass
from cocotbext.ofm.base.transaction import Transaction
from cocotbext.ofm.utils.hex_formatter import format_bytes


@dataclass
class Axi4StreamBaseTransaction(Transaction):
    """
    Base class for Axi4Stream transactions.
    """


@dataclass
class Axi4StreamTransaction(Axi4StreamBaseTransaction):
    """
    Axi4Stream transaction with TDATA and TUSER.
    """
    TDATA: bytes = b''
    TUSER: bytes = b''

    def __repr__(self) -> str:
        """Return formatted hex representation of the transaction."""
        parts = []
        if self.TUSER:
            parts.append(format_bytes(self.TUSER, label="TUSER"))
        if self.TDATA:
            parts.append(format_bytes(self.TDATA, label="TDATA"))
        return '\n'.join(parts) if parts else super().__repr__()


@dataclass
class Axi4StreamTransactionWithSelect(Axi4StreamTransaction):
    """
    Axi4Stream transaction with TDATA, TUSER and selector SEL.
    """
    SEL: int = 0

    def __repr__(self) -> str:
        """Return formatted hex representation of the transaction."""
        parts = [super().__repr__()]
        parts.append(f"SEL: {self.SEL}")
        return '\n'.join(parts)
