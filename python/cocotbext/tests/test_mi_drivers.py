# test_mi_drivers.py: unit test of the MI request driver on a stub 64-bit bus
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

import asyncio
import logging
from types import SimpleNamespace

import pytest
from cocotb.types import LogicArray

from cocotbext.ofm.base.drivers import BusDriver
from cocotbext.ofm.mi.drivers import MIPipelinedDriver, MIRequestDriver
from stubs import StubSignal

DATA_BYTES = 8
WORD = bytes(range(0x10, 0x10 + DATA_BYTES))


class Edge:
    """A clock edge that has always just passed, so the driver never waits."""

    def __await__(self):
        yield from ()


class Bus:
    """A 64-bit MI bus whose slave accepts every request at once and answers every read with WORD."""

    def __init__(self):
        self.addr = StubSignal(32)
        self.dwr = StubSignal(DATA_BYTES * 8)
        self.be = StubSignal(DATA_BYTES)
        self.wr = StubSignal(1)
        self.rd = StubSignal(1)
        self.ardy = StubSignal(1, 1)
        self.drd = StubSignal(DATA_BYTES * 8, LogicArray.from_bytes(WORD, byteorder="little"))
        self.drdy = StubSignal(1, 1)

    def read_requests(self):
        """(ADDR, BE) of every read request; the driver writes all its outputs together, so the n-th writes match."""
        return [(a, be) for a, be, rd in zip(self.addr.written, self.be.written, self.rd.written) if rd]


def _bus_driver_init(self, entity, name, clock, array_idx=None, **kwargs):
    self.bus, self._clk_re, self.log = entity, clock, logging.getLogger("test_mi_drivers")


@pytest.fixture
def driver(monkeypatch):
    monkeypatch.setattr(BusDriver, "__init__", _bus_driver_init)
    return MIRequestDriver(Bus(), "IN", Edge())


@pytest.mark.parametrize("addr, byte_count, byte_enable, requests", [
    (0x100, 8, None, [(0x100, 0xFF)]),
    (0x104, 4, None, [(0x100, 0xF0)]),
    (0x106, 4, 0b1011, [(0x100, 0xC0), (0x108, 0x02)]),
])
def test_read_enables_the_requested_lanes_of_a_64_bit_bus(driver, addr, byte_count, byte_enable, requests):
    data = asyncio.run(driver.read(addr, byte_count, byte_enable=byte_enable))

    assert driver.bus.read_requests() == requests
    start = addr % DATA_BYTES
    assert data == (WORD * len(requests))[start:start + byte_count]


def test_pipelined_requests_follow_each_other_at_ardy(monkeypatch):
    monkeypatch.setattr(BusDriver, "__init__", _bus_driver_init)
    drv = MIPipelinedDriver(Bus(), "IN", Edge())
    ops = [SimpleNamespace(write=True, addr=0x10, data=0xA5), SimpleNamespace(write=False, addr=0x18, data=0)]
    accepted = []

    asyncio.run(drv.issue(ops, accepted.append))

    assert accepted == ops
    assert drv.bus.addr.written[-2:] == [0x10, 0x18] and drv.bus.be.written[-1] == (1 << DATA_BYTES) - 1
    assert drv.bus.wr.written[-3:] == [1, 0, 0] and drv.bus.rd.written[-3:] == [0, 1, 0]
