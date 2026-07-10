# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#            Ondrej Schwarz <ondrejschwarz@cesnet.cz>

import cocotb
import warnings
import cocotb_bus.drivers as cbd
import cocotb_bus.monitors as cbm
from cocotb_bus.bus import Bus
from cocotb_bus.monitors import MonitorStatistics

from collections import deque
from typing import Optional
from cocotb.triggers import Event

from cocotb.types import LogicArray


class Driver:
    def __init__(self):
        """Constructor for a driver instance."""
        self._pending = Event()
        self._sendQ = deque()
        self.busy_event = Event()
        self.busy = False

        # Create an independent coroutine which can send stuff
        self._thread = cocotb.start_soon(self._send_thread())


class Monitor:
    def __init__(self, callback=None, event=None):
        self._event = event
        self._wait_event = Event()
        self._recvQ = deque()
        self._callbacks = []
        self.stats = MonitorStatistics()

        if callback is not None:
            self.add_callback(callback)

        # Create an independent coroutine which can receive stuff
        self._thread = cocotb.start_soon(self._monitor_recv())


def do_fix():
    cbd.Driver.__init__ = Driver.__init__
    cbm.Monitor.__init__ = Monitor.__init__


# cocotb 2.0-only defines
if cocotb.__version__ >= "2.0.0":
    from cocotb.handle import ArrayObject, Immediate

    class SignalProxy:
        _instances = {}

        def __new__(cls, handle, array_idx=None):
            key = (id(handle), array_idx)
            if key not in cls._instances:
                cls._instances[key] = super().__new__(cls)
            return cls._instances[key]

        def __init__(self, handle, array_idx: Optional[int] = None):
            self._handle = handle
            self._array_idx = array_idx

        def __len__(self):
            return len(self.value)

        @property
        def value(self):
            if self._array_idx is not None:
                return LogicArray(str(self._handle.value[self._array_idx]))
            else:
                return LogicArray(str(self._handle.value))

        @value.setter
        def value(self, val):
            # workaround for compatibility with cocotb 1.9.2
            if isinstance(val, LogicArray):
                val = str(val)

            if self._array_idx is not None:
                full_val = self._handle.value
                full_val[self._array_idx] = val

                # so multiple drivers can read value edited by other drivers
                self._handle.set(Immediate(full_val))
            else:
                self._handle.set(Immediate(val))

        def set(self, value):
            self._handle.set(value)

        def setimmediatevalue(self, value):
            warnings.warn("Method setimmediatevalue(value) is deprecated in cocotb 2.0, use set(Immediate(value)) instead.", DeprecationWarning)
            self._handle.set(Immediate(value))

    class BusProxy:
        def __init__(self, bus: Bus, array_idx: Optional[int] = None):
            self._bus = bus
            self._array_idx = array_idx

        def __getattr__(self, name: str):
            handle = getattr(self._bus, name)

            if isinstance(handle, ArrayObject):
                return handle[self._array_idx]

            return SignalProxy(handle, self._array_idx)
