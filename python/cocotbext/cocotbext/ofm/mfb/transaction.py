# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>

from ..base.transaction import Transaction


class MfbTransaction(Transaction):
    attrs = ["data"]

    def __init__(self, **kwargs):
        for i in self.attrs:
            setattr(self, i, 0)

        for attr, value in kwargs.items():
            setattr(self, attr, value)

    def __eq__(self, other):
        if isinstance(other, MfbTransaction):
            for attr in self.attrs:
                if getattr(self, attr) != getattr(other, attr):
                    return False
            return True
        return NotImplemented

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


class MfbTransactionWithMeta(MfbTransaction):
    attrs = ["data", "meta"]
