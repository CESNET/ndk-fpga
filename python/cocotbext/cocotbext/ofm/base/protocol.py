# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <ondrej.schwarz@cesnet.cz>

from typing import Optional
from copy import copy
from .descriptors import BusParameter, GenericDescriptor, SignalDescriptor, DescriptorAlias


class GenericDecorator:
    """Decorator factory marking a protocol attribute as a VHDL generic.

    Applied as ``generic()`` on a protocol class attribute. The attribute
    name (optionally prefixed with the bus's ``generics_prefix``) is used
    to look up the generic's value on the DUT.
    """

    def __call__(self, func=None):
        return GenericDescriptor(func)


class SignalDecorator:
    """Decorator factory marking a protocol attribute as a mandatory bus signal.

    Applied as ``signal()`` or ``@signal`` on a protocol class attribute.
    The attribute name (prefixed with the bus name) is used to resolve the
    signal handle on the DUT. A missing mandatory signal raises an error.

    Use ``signal.read(put_with=...)`` / ``signal.write(put_with=...)``
    to attach custom read/write transformation functions.

    The ``put_with`` parameter names another signal of the protocol that
    validates this one (e.g. ``put_with="vld"``). When set, drivers and
    monitors automatically transfer the signal's value between the
    transaction and the bus only in clock cycles where the validating
    signal is asserted. When ``None`` (the default), no automatic
    placement is performed — the signal's value is put on the bus manually
    (e.g. by the driver's ``_split_transaction`` implementation).
    """

    is_optional = False

    @classmethod
    def read(cls, put_with=None):
        def decorator(func):
            return SignalDescriptor(read_func=func, is_optional=cls.is_optional, put_with=put_with)
        return decorator

    @classmethod
    def write(cls, put_with=None):
        def decorator(func):
            return SignalDescriptor(write_func=func, is_optional=cls.is_optional, put_with=put_with)
        return decorator

    def __call__(self, func=None, put_with=None):
        # used directly as a decorator: @signal / @optional_signal
        if callable(func):
            return SignalDescriptor(read_func=func, is_optional=self.is_optional, put_with=put_with)
        # used as a factory for assignment: SIG = signal(put_with="...")
        if func is not None:
            raise TypeError(f"Expected a callable or None, got {type(func).__name__!r}. "
                            "Use keyword argument, e.g. signal(put_with='TVALID').")
        return SignalDescriptor(is_optional=self.is_optional, put_with=put_with)


class OptionalSignalDecorator(SignalDecorator):
    """Decorator factory marking a protocol attribute as an optional bus signal.

    Behaves like :class:`SignalDecorator`, but a signal that is not present
    on the DUT only produces a warning instead of an error. This allows one
    protocol definition to cover buses with slightly different signal sets.
    """

    is_optional = True


class DescriptorAliasDecorator:
    """Decorator factory creating an alias for an existing protocol descriptor.

    Used when the DUT names a signal or generic differently than the
    protocol attribute, e.g. ``pcie_down_regions: int = alias(MvbProtocol.items)``
    maps the DUT's ``PCIE_DOWN_REGIONS`` generic onto the ``items`` attribute.
    """

    def __call__(self, alias_to):
        return DescriptorAlias(alias_to)


def parameter(func):
    return BusParameter(func)


generic = GenericDecorator()
signal = SignalDecorator()
optional_signal = OptionalSignalDecorator()
alias = DescriptorAliasDecorator()


class BusProtocol:
    """Base class describing the signals and generics of a bus interface.

    Subclasses declare protocol attributes using the ``generic()``,
    ``signal()``, ``optional_signal()`` and ``alias()`` decorators. On
    instantiation, all declared attributes are resolved against the DUT:
    signal names are constructed as ``{bus_name}{separator}{ATTR_NAME}``
    and generics as ``{generics_prefix}{separator}{ATTR_NAME}``.

    Resolved signals are collected into ``signals`` (all) and
    ``optional_signals`` (only optional ones), sorted so that signals with
    a ``put_with`` dependency come after the signal they depend on.
    Drivers and monitors use these dictionaries to automatically read and
    write bus signals from/to transactions.

    Args:
        dut: The DUT handle (cocotb hierarchy object).
        name: Bus name prefix used to resolve signal names on the DUT.
        separator: Separator between the bus name and the attribute name.
        array_idx: Index into an arrayed bus (for multi-instance interfaces).
        generics_prefix: Prefix prepended to generic names on the DUT.
    """

    def __init__(self, dut, name: str, separator: str = "_", array_idx: Optional[int] = None, generics_prefix: str = ""):
        self.dut  = dut
        self.name = name
        self.separator = separator
        self.array_idx = array_idx
        self.generics_prefix = generics_prefix

        self.parameters = {}
        # all present generics
        self.generics = {}
        # all of the signals on the bus (mandatory and optional)
        self.signals = {}
        # only optional signals on the bus
        self.optional_signals = {}
        # aliases of signals
        self.aliases = {}

        for attr_name in dir(self.__class__):
            attr_val = getattr(self.__class__, attr_name, None)

            if isinstance(attr_val, BusParameter):
                self.parameters[attr_name] = attr_val

            elif isinstance(attr_val, GenericDescriptor):
                generic = attr_val.resolve(self)

                if generic is None:
                    continue

                self.generics[attr_name] = attr_val

            elif isinstance(attr_val, SignalDescriptor):
                signal = attr_val.resolve(self)

                # if no alias has been found on bus
                if signal is None:
                    continue

                # filter out null signals
                if len(signal) <= 0:
                    continue

                self.signals[attr_name] = attr_val

        self._sort_signals_by_dependency()

    def __getitem__(self, index: int):
        assert self.array_idx is None, "Cannot index a protocol that has already been indexed."

        new_instance = copy(self)
        new_instance.array_idx = index

        return new_instance

    def _sort_signals_by_dependency(self):
        sorted_signals = dict()

        # get all signals that don't need validation first
        for name, descriptor in self.signals.items():
            if descriptor.put_with is None:
                sorted_signals[name] = descriptor

        for name in sorted_signals.keys():
            del self.signals[name]

        # get all signals dependend of something in the correct order
        while self.signals:
            to_be_added = list()

            for name, descriptor in self.signals.items():
                if descriptor.put_with in sorted_signals.keys():
                    to_be_added.append(name)

            # no progress means the remaining signals either form a dependency
            # cycle or depend on a signal that doesn't exist in the protocol
            if not to_be_added:
                self._raise_dependency_error()

            for name in to_be_added:
                sorted_signals[name] = self.signals[name]
                del self.signals[name]

        self.signals = sorted_signals

        # creating optional signals dictionary
        self.optional_signals = dict()

        for name, descriptor in self.signals.items():
            if descriptor.is_optional:
                self.optional_signals[name] = descriptor

    def _raise_dependency_error(self):
        """Report unresolved or circular put_with dependencies of the remaining signals."""
        # signals depending on a name that doesn't exist in the protocol
        unknown = {
            name: descriptor.put_with
            for name, descriptor in self.signals.items()
            if descriptor.put_with not in self.signals
        }

        if unknown:
            details = ", ".join(f"'{name}' (put_with='{dep}')" for name, dep in unknown.items())
            raise ValueError(
                f"Signals with unresolved 'put_with' dependency: {details}. "
                "The referenced signal is not part of the protocol (typo, zero-width "
                "signal, or an optional signal not present on the bus)."
            )

        # all remaining signals depend on each other -> there must be a cycle
        cycle = self._find_dependency_cycle()
        raise ValueError(f"Circular 'put_with' dependency detected: {' -> '.join(cycle)}")

    def _find_dependency_cycle(self) -> list:
        """Follow put_with chains of the remaining signals to find one cycle."""
        for start in self.signals:
            path = []
            current = start

            while current in self.signals:
                if current in path:
                    return path[path.index(current):] + [current]

                path.append(current)
                current = self.signals[current].put_with

        return []

    def put_with(self, signal_name: str) -> bool:
        """Return whether the given signal is currently valid according to its put_with."""
        descriptor = self.signals.get(signal_name)
        return descriptor.put_with

    def get_signal_descriptor(self, name: str):
        return self.signals.get(name)

    def get_signal_value(self, name: str):
        descriptor = self.get_signal_descriptor(name)
        return descriptor.__get__(self)

    def set_signal_value(self, name, value):
        descriptor = self.get_signal_descriptor(name)
        descriptor.__set__(self, value)
