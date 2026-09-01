# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Martin Spinler <spinler@cesnet.cz>
#            Ondrej Schwarz <ondrejschwarz@cesnet.cz>

import cocotb
import warnings
import logging
import cocotb_bus.drivers as cbd
import cocotb_bus.monitors as cbm
from cocotb_bus.bus import Bus
from cocotb_bus.monitors import MonitorStatistics

from collections import deque
from typing import Optional, Callable
from functools import cached_property
from cocotb.triggers import Event


class Driver:
    def __init__(self):
        """Constructor for a driver instance."""
        self._pending = Event()
        self._sendQ = deque()
        self.busy_event = Event()
        self.busy = False

        # Sub-classes may already set up logging
        if not hasattr(self, "log"):
            self.log = logging.getLogger("cocotb.driver.%s" % (type(self).__qualname__))

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

        # Sub-classes may already set up logging
        if not hasattr(self, "log"):
            self.log = logging.getLogger("cocotb.monitor.%s" % (type(self).__qualname__))

        # Create an independent coroutine which can receive stuff
        self._thread = cocotb.start_soon(self._monitor_recv())


def do_fix():
    cbd.Driver.__init__ = Driver.__init__
    cbm.Monitor.__init__ = Monitor.__init__


# cocotb 2.0-only defines
if cocotb.__version__ >= "2.0.0":
    from cocotb.types import Logic, LogicArray
    from cocotb.handle import LogicObject, ArrayObject, Immediate, Deposit
    from cocotb.triggers import GPITrigger
    from cocotb._gpi_triggers import _EdgeBase
    from cocotb.simulator import register_value_change_callback, VALUE_CHANGE, RISING, FALLING

    class _EdgeProxyBase(_EdgeBase):
        _instances = {}
        _cbhdls = {}
        _can_fire = set()

        def _is_edge_event(self, last_value, current_value) -> bool:
            return last_value != current_value

        @property
        def _path(self):
            return self.signal._path

        @classmethod
        def _make(cls, signal):
            self = GPITrigger.__new__(cls)
            GPITrigger.__init__(self)

            self.signal = signal
            self._last_val = int(self.signal.value)

            if self._path not in cls._instances.keys():
                cls._instances[self._path] = list()

            cls._instances[self._path].append(self)

            if self._path not in cls._cbhdls.keys():
                cls._cbhdls[self._path] = None

            return self

        if hasattr(_EdgeBase, "_react"):
            def _prime(self) -> None:
                cls = type(self)

                cls._can_fire.add(self)

                self._last_val = int(self.signal.value)

                if cls._cbhdls[self._path] is None:
                    cls._cbhdls[self._path] = register_value_change_callback(
                        self.signal._handle, cls._distribute_callback, VALUE_CHANGE, self
                    )
                    if cls._cbhdls[self._path] is None:
                        raise RuntimeError(f"Unable set up {self!s} Trigger")

            @classmethod
            def _distribute_callback(cls, trigger: "_EdgeProxyBase"):
                is_primed = False
                path = trigger._path
                instances = cls._instances[path]

                cls._cbhdls[path] = None

                for instance in instances:
                    is_primed |= instance._do_callback()

                if not is_primed:
                    trigger._prime()

            def _do_callback(self) -> bool:
                cls = type(self)
                did_callback = False
                current = int(self.signal.value)

                if self._is_edge_event(self._last_val, current) and self in cls._can_fire:
                    self._react()
                    did_callback = True

                self._last_val = current
                return did_callback
        else:
            def _prime(self, callback: Callable) -> None:
                cls = type(self)

                cls._can_fire.add(self)

                self._last_val = int(self.signal.value)

                if cls._cbhdls[self._path] is None:
                    cls._cbhdls[self._path] = register_value_change_callback(
                        self.signal._handle, lambda trigger: cls._distribute_callback(trigger, callback), VALUE_CHANGE, self
                    )
                    if cls._cbhdls[self._path] is None:
                        raise RuntimeError(f"Unable set up {self!s} Trigger")

            @classmethod
            def _distribute_callback(cls, trigger: "_EdgeProxyBase", callback: Callable):
                is_primed = False
                path = trigger._path
                instances = cls._instances[path]

                cls._cbhdls[path] = None

                for instance in instances:
                    is_primed |= instance._do_callback(callback)

                if not is_primed:
                    trigger._prime(callback)

            def _do_callback(self, callback: Callable) -> bool:
                cls = type(self)
                did_callback = False
                current = int(self.signal.value)

                if self._is_edge_event(self._last_val, current) and self in cls._can_fire:
                    callback(self)
                    did_callback = True

                self._last_val = current
                return did_callback

        def _unprime(self):
            self._can_fire.discard(self)

    class RisingEdgeProxy(_EdgeProxyBase):
        _edge_type = RISING

        def __new__(cls, signal: cocotb.handle.LogicObject) -> "RisingEdgeProxy":
            if not isinstance(
                signal, (cocotb.handle.LogicObject, cocotb.handle.LogicArrayObject)
            ):
                raise TypeError(
                    f"{cls.__qualname__} requires a scalar LogicObject or a 1-bit LogicArrayObject. Got {signal!r} of type {type(signal).__qualname__}"
                )
            return signal.rising_edge

        def _is_edge_event(self, last_value, current_value) -> bool:
            return last_value == 0 and current_value == 1

    class FallingEdgeProxy(_EdgeProxyBase):
        _edge_type = FALLING

        def __new__(cls, signal: cocotb.handle.LogicObject) -> "FallingEdgeProxy":
            if not isinstance(
                signal, (cocotb.handle.LogicObject, cocotb.handle.LogicArrayObject)
            ):
                raise TypeError(
                    f"{cls.__qualname__} requires a scalar LogicObject or a 1-bit LogicArrayObject. Got {signal!r} of type {type(signal).__qualname__}"
                )
            return signal.falling_edge

        def _is_edge_event(self, last_value, current_value) -> bool:
            return last_value == 1 and current_value == 0

    class LogicProxy(LogicObject):
        _instances = {}

        def __new__(cls, handle, array_idx):
            if handle is None:
                return None

            key = (id(handle), array_idx)
            if key not in cls._instances:
                cls._instances[key] = super().__new__(cls)
            return cls._instances[key]

        def __init__(self, handle, array_idx):
            # Indexed path so cocotb2path / edge-trigger keys resolve the bit, not the parent vector
            super().__init__(handle._handle, f"{handle._path}[{array_idx}]")
            self._lao_handle = handle
            self._array_idx = array_idx

        @property
        def value(self):
            return Logic(str(self._lao_handle.value[self._array_idx]))

        @value.setter
        def value(self, value):
            self.set(value)

        def set(self, value):
            if isinstance(value, Deposit) or isinstance(value, Immediate):
                value  = value.value

            full_val = self._lao_handle.value
            full_val[self._array_idx] = value
            self._lao_handle.set(Immediate(full_val))

        @cached_property
        def rising_edge(self):
            return RisingEdgeProxy._make(self)

        @cached_property
        def falling_edge(self):
            return FallingEdgeProxy._make(self)

    class SignalProxy:
        _instances = {}

        def __new__(cls, handle, array_idx=None):
            if handle is None:
                return None

            key = (id(handle), array_idx)
            if key not in cls._instances:
                cls._instances[key] = super().__new__(cls)
            return cls._instances[key]

        def __init__(self, handle, array_idx: Optional[int] = None):
            self._handle = handle
            self._array_idx = array_idx

        def __len__(self):
            return len(self.value)

        def __getitem__(self, index: int):
            if isinstance(self._handle, ArrayObject):
                return SignalProxy(self._handle, index)
            return LogicProxy(self._handle, index)

        @property
        def _path(self):
            if self._array_idx is not None:
                return f"{self._handle._path}[{self._array_idx}]"
            return self._handle._path

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
            if self._array_idx is None:
                self._handle.set(value)
                return

            # Update only this slice
            full_val = self._handle.value
            if isinstance(value, (Deposit, Immediate)):
                full_val[self._array_idx] = value.value
            else:
                full_val[self._array_idx] = value
            self._handle.set(Immediate(full_val))

        def setimmediatevalue(self, value):
            warnings.warn("Method setimmediatevalue(value) is deprecated in cocotb 2.0, use set(Immediate(value)) instead.", DeprecationWarning)
            self.set(Immediate(value))

    class BusProxy:
        def __init__(self, bus: Bus, array_idx: Optional[int] = None):
            self._bus = bus
            self._array_idx = array_idx

        def __getattr__(self, name: str):
            handle = getattr(self._bus, name)

            if isinstance(handle, ArrayObject):
                if self._array_idx is not None:
                    return handle[self._array_idx]
                else:
                    return handle

            return SignalProxy(handle, self._array_idx)
