# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <ondrej.schwarz@cesnet.cz>

import warnings
from cocotb.handle import ArrayObject
from .bus_fixup import SignalProxy


class BusParameter:
    """
    Descriptor that acts as a property for bus-related metadata.

    Unlike other descriptors, it does not retrieve data from the DUT.
    Instead, it is used for values calculated from other attributes
    (e.g., derived from generics) or static configuration of the bus.
    """

    def __init__(self, func):
        self._func = func
        self._func._is_parameter = True

    def __get__(self, instance, owner=None):
        if instance is None:
            return self
        return self._func(instance)


class BaseDescriptor:
    """
    Base class for descriptors that retrieve data from the DUT.

    It provides a common implementation for resolving signal or generic
    handles on the DUT. The target name is derived from the variable name
    used in the protocol definition, combined with the bus instance prefix.
    """
    def __init__(self):
        self.name           = None
        self._aliases       = list()
        self._resolve_cache = dict()

    def __set_name__(self, owner, name):
        self.name = name

    def add_alias(self, alias: "DescriptorAlias"):
        self._aliases.append(alias)

    def resolve(self, bus):
        cache_key = (bus.name, bus.array_idx)

        if cache_key in self._resolve_cache.keys():
            return self._resolve_cache[cache_key]

        self._resolve_cache[cache_key] = self._get_handle(bus, self.name)

        if self._resolve_cache[cache_key] is not None:
            return self._resolve_cache[cache_key]

        # if not found, check aliases
        for alias in self._aliases:
            self._resolve_cache[cache_key] = self._get_handle(bus, alias.name)

            if self._resolve_cache[cache_key] is not None:
                return self._resolve_cache[cache_key]

        # if not found
        return None

    def alias(self):
        return DescriptorAlias(alias_to=self)

    def _get_handle(self, bus, name: str, prefix: str = ""):
        """
        Resolves the signal handle on the DUT.

        The final signal name is constructed as {prefix}{name}, where 'name'
        is the name of the variable in the protocol class. This allows
        the protocol to define a generic name (e.g., TDATA) which is
        then mapped to the DUT signal (e.g., RX_AXI_TDATA) using the
        bus instance prefix.
        """
        name_upper  = f"{prefix}{name.upper()}"
        name_lower  = f"{prefix}{name.lower()}"

        # try to find the signal on the dut
        if hasattr(bus.dut, name_upper):
            return getattr(bus.dut, name_upper)
        elif hasattr(bus.dut, name_lower):
            return getattr(bus.dut, name_lower)

        return None


class GenericDescriptor(BaseDescriptor):
    """
    Descriptor for automatically retrieving VHDL generic values.

    It resolves the generic handle on the DUT. If the generic on the DUT
    has a different name than the protocol variable (e.g., MFB_REGIONS
    instead of REGIONS), the `generics_prefix` can be used to match it.
    """
    def __init__(self, func=None):
        super().__init__()
        self._func = func

    def __get__(self, bus, owner=None):
        if bus is None:
            return self

        handle = self.resolve(bus)

        if handle is None:
            return None

        if self._func is not None:
            return self._func(bus, handle.value)

        return handle.value

    def resolve(self, bus):
        result = super().resolve(bus)

        if result is None:
            warnings.warn(f"Failed to resolve generic {self.name}, because it's not present on dut.")

        return result

    def _get_handle(self, bus, name, prefix=""):
        if prefix:
            prefix = f"{prefix}{bus.separator}"
        else:
            prefix = f"{bus.generics_prefix}{bus.separator}" if bus.generics_prefix else ""

        return super()._get_handle(bus, name, prefix)


class SignalDescriptor(BaseDescriptor):
    """
    Descriptor for reading and writing signal values on the DUT.

    Supports custom read/write transformation functions.

    Optionality:
    - Mandatory signals: If not found on the DUT, an AttributeError is raised.
    - Optional signals: If not found, a warning is issued. Reading returns None,
      and writing has no effect.

    Validation (put_with):
    - If `put_with` names another signal of the protocol (e.g., "vld"),
      drivers and monitors automatically transfer the signal's value between
      the transaction and the bus only in clock cycles where the validating
      signal is asserted.
    - If `put_with` is None (the default), no automatic placement is
      performed — the signal's value is put on the bus manually (e.g., by
      the driver's `_split_transaction` implementation).
    """

    _existing = {}

    def __init__(self, read_func=None, write_func=None, is_optional: bool = False, put_with=None):
        super().__init__()
        self.is_optional = is_optional
        self.put_with  = put_with
        self._read_func  = read_func
        self._write_func = write_func

    def __set_name__(self, owner, name):
        self.name = name
        key = (owner, name)
        existing = SignalDescriptor._existing.get(key)
        if isinstance(existing, SignalDescriptor):
            if self._read_func is None:
                self._read_func = existing._read_func
            if self._write_func is None:
                self._write_func = existing._write_func
        SignalDescriptor._existing[key] = self

    def __get__(self, bus, owner=None):
        if bus is None:
            return self

        sig = self.resolve(bus)

        if sig is None:
            return None

        sigval = sig.value if bus.array_idx is None else sig.value[bus.array_idx]

        if self._read_func is not None:
            return self._read_func(bus, sigval)

        return sigval

    def __set__(self, bus, value):
        sig = self.resolve(bus)

        if sig is None:
            return

        if bus.array_idx is not None:
            if isinstance(sig, ArrayObject):
                sig = sig[bus.array_idx]
            else:
                sig = SignalProxy(sig, bus.array_idx)

        if self._write_func is not None:
            self._write_func(bus, sig, value)
        else:
            sig.value = value

    def resolve(self, bus):
        result = super().resolve(bus)

        # if the signal wasn't found
        if result is None:
            if self.is_optional:
                warnings.warn(f"Failed to resolve optional signal {self.name}, because it's not present on bus.")
            else:
                raise AttributeError(f"Failed to resolve signal {self.name}, because it's not present on bus.")

        return result

    def read(self, put_with=None):
        """Decorator adding a read function to this signal descriptor."""
        def decorator(func):
            return SignalDescriptor(read_func=func, write_func=self._write_func, is_optional=self.is_optional, put_with=self.put_with if put_with is None else put_with)
        return decorator

    def write(self, put_with=None):
        """Decorator adding a write function to this signal descriptor."""
        def decorator(func):
            return SignalDescriptor(read_func=self._read_func, write_func=func, is_optional=self.is_optional, put_with=self.put_with if put_with is None else put_with)
        return decorator

    def _get_put_with_value(self, bus):
        if self.put_with is not None:
            return self.put_with.__get__(bus)

    def _get_handle(self, bus, name, prefix=""):
        prefix = f"{bus.name}{bus.separator}" if len(prefix) == 0 else f"{prefix}{bus.separator}"
        return super()._get_handle(bus, name, prefix)


class DescriptorAlias:
    """
    Provides an alias for an existing descriptor.

    This is used when a signal has a generic name in the protocol (e.g., TDATA)
    but a different name on the actual DUT (e.g., AXI_TDATA). The alias
    maps the protocol's name to the DUT's specific signal name, allowing
    the driver to use consistent naming regardless of the component's
    internal naming conventions.
    """
    def __init__(self, alias_to):
        self._alias_to = alias_to
        alias_to.add_alias(self)

    def __set_name__(self, owner, name):
        self.name = name

    def __get__(self, bus, owner):
        return self._alias_to.__get__(bus)

    def __set__(self, bus, value):
        self._alias_to.__set__(bus, value)
