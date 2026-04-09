# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>

from dataclasses import dataclass
from ..base.transaction import Transaction


@dataclass(slots=True)
class MfbTransaction(Transaction):
    data: bytes = b""

    def __repr__(self):
        ret = ""
        if hasattr(self, "meta"):
            ret += "META:\n"
            # ret += "{}".format(self.meta.to_bytes((self.meta.bit_length() + 7) // 8, byteorder='little'))
            ret += "{:x}".format(self.meta)

        if hasattr(self, "data"):
            ret += "\nDATA:\n"
            conv_hex = self.data.hex()
            # Join every 8-character group with a space
            with_space = ' '.join([conv_hex[i:i+8] for i in range(0, len(conv_hex), 8)])
            # Join every 64-character section with a newline
            formatted_string = '\n'.join([with_space[i:i+64+8] for i in range(0, len(with_space), 64+8)])

            ret += formatted_string

        return f"{ret}"


@dataclass(slots=True)
class MfbTransactionWithMeta(MfbTransaction):
    meta: int = 0
