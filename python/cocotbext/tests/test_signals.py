# test_signals.py: unit test of get_signal_value_in_bytes
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

from cocotb.types import LogicArray

from cocotbext.ofm.utils.signals import get_signal_value_in_bytes
from stubs import StubSignal


def test_signal_value_is_little_endian_by_default():
    sig = StubSignal(16, LogicArray.from_unsigned(0x0102, 16))
    assert get_signal_value_in_bytes(sig) == b"\x02\x01"
    assert get_signal_value_in_bytes(sig, big_endian=True) == b"\x01\x02"
