# test_header.py: unit test of SerializableHeader
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

from cocotbext.ofm.utils.header import SerializableHeader


class Header(SerializableHeader):
    items = [("first", 8), ("second", 4)]


def test_offsets_follow_the_field_order():
    header = Header()
    header.first = 0x5A
    header.second = 0x3

    assert Header.offsets() == {"first": 0, "second": 8}
    assert header.serialize() == (0x3 << Header.offsets()["second"]) | 0x5A


def test_header_is_printed_on_one_line():
    header = Header()
    header.first = 255
    header.second = 3

    assert str(header) == "first: 255 (0xff), second: 3 (0x3)"
