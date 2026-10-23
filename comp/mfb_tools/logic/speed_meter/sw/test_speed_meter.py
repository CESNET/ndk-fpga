# test_speed_meter.py: unit test of the byte counter readout of the SpeedMeter class
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

import pytest
from ofm.comp.mfb_tools.logic.speed_meter.speed_meter import SpeedMeter


class StubNode:
    """Device Tree node that carries only the reg property"""

    def __init__(self, reg):
        self._reg = reg

    def get_property(self, name):
        assert name == "reg"
        return self._reg


class StubComp:
    """Component whose registers behave like the firmware: a read behind the mapped region fails"""

    def __init__(self, size, registers):
        self.size = size
        self.registers = registers
        self.reads = []

    def read32(self, addr):
        self.reads.append(addr)
        assert addr + 4 <= self.size, "read behind the component region"
        return self.registers.get(addr, 0)


def make_meter(size, registers, reg=..., lightweight=False):
    meter = SpeedMeter.__new__(SpeedMeter)
    meter._lightweight = lightweight
    meter._comp = StubComp(size, registers)
    meter._node = StubNode([0x1000, size] if reg is ... else reg)
    return meter


def test_wide_counter_reads_both_words():
    meter = make_meter(0x20, {0x08: 0x89ABCDEF, 0x1C: 0x1234})
    assert meter.items == (0x1234 << 32) | 0x89ABCDEF


def test_old_firmware_is_read_without_the_high_word():
    meter = make_meter(0x1C, {0x08: 0x89ABCDEF})
    assert meter.items == 0x89ABCDEF
    assert 0x1C not in meter._comp.reads


def test_missing_reg_property_reads_only_the_low_word():
    meter = make_meter(0x20, {0x08: 7, 0x1C: 5}, reg=None)
    assert meter.items == 7


@pytest.mark.parametrize("size", [0x20, 0x40, 0x1000])
def test_larger_region_keeps_the_high_word(size):
    assert make_meter(size, {0x08: 1, 0x1C: 2}).items == (2 << 32) | 1


def test_high_word_is_zero_for_a_32_bit_counter():
    assert make_meter(0x20, {0x08: 0xFFFFFFFF}).items == 0xFFFFFFFF


def test_lightweight_meter_reads_only_the_low_word():
    # gen_loop_switch places its lightweight meters 0x10 apart, so 0x1C holds a register of the next meter.
    meter = make_meter(0x20, {0x08: 0x89ABCDEF, 0x1C: 0x1234}, lightweight=True)
    assert meter.items == 0x89ABCDEF
    assert 0x1C not in meter._comp.reads
