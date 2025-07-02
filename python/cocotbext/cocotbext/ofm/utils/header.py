# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#            Daniel Kondys <kondys@cesnet.cz>

import operator
from functools import reduce


def concat(values):
    ret = 0
    for val, width in reversed(values):
        ret <<= width
        ret |= val & (2**width - 1)
    return ret


def deconcat(values=[0, 0]):
    vector = values[0]
    ret = []
    for width in values[1:]:
        ret.append(vector & (2**width - 1))
        vector >>= width
    return ret


def byte_serialize(data, length):
    return [(data >> (8 * i)) & 0xFF for i in range(length)]


def byte_deserialize(data):
    return reduce(
        operator.or_, [(data[i] & 0xFF) << (8 * i) for i in range(len(data))], 0
    )


class SerializableHeader(object):
    items = []

    def __init__(self):
        for i in self.items:
            setattr(self, i[0], 0)

    def __str__(self):
        pnt = [f"{item[0]}: {getattr(self, item[0])} (0x{getattr(self, item[0]):x})" for item in self.items]
        return '\n'.join(pnt)

    def serialize(self):
        names, widths = list(zip(*self.items)) if self.items else ([], [])
        return concat(list(zip([getattr(self, name) for name in names], widths)))

    @classmethod
    def __len__(cls):
        return sum([x[1] for x in cls.items])

    @classmethod
    def deserialize(cls, val: int):
        ret = cls()
        for i in cls.items:
            setattr(ret, i[0], val & 2 ** i[1] - 1)
            val >>= i[1]
        return ret
