# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>

from dataclasses import dataclass
from ..base.transaction import Transaction
from ..utils.hex_formatter import format_bytes


@dataclass(slots=True)
class MfbTransaction(Transaction):
    data: bytes = b""

    def __repr__(self) -> str:
        """Return formatted hex representation of the transaction."""
        # MfbTransaction does not have meta attribute, only MfbTransactionWithMeta does
        if hasattr(self, "data") and self.data:
            return format_bytes(self.data, label="DATA")
        return super().__repr__()


@dataclass(slots=True)
class MfbTransactionWithMeta(MfbTransaction):
    meta: int = 0

    def __repr__(self) -> str:
        """Return formatted hex representation of the transaction."""
        # Convert meta to bytes - handle 0 as special case (0.bit_length() returns 0)
        meta_bytes = (
            self.meta.to_bytes(1, byteorder='big') if self.meta == 0
            else self.meta.to_bytes((self.meta.bit_length() + 7) // 8, byteorder='big')
        )
        ret = format_bytes(meta_bytes, label="META")
        ret += "\n"

        if hasattr(self, "data") and self.data:
            ret += format_bytes(self.data, label="DATA")

        return ret
