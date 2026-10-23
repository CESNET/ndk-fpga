# stubs.py: stand-ins for simulator signals in the unit tests of cocotbext
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

from types import SimpleNamespace


class StubSignal:
    """Stands in for a signal handle: a value that keeps every write, a width, a logger and the bit string a
    simulator hands over (`binstr`), so code that reads the raw handle sees it too."""

    log = SimpleNamespace(error=lambda *args: None)

    def __init__(self, width=0, value=0):
        self.width = width
        self.written = []
        self._value = value
        self.binstr = "0" * width
        self._handle = self

    @property
    def value(self):
        return self._value

    @value.setter
    def value(self, value):
        self._value = value
        self.written.append(int(value))

    def get_signal_val_binstr(self):
        return self.binstr

    def __len__(self):
        return self.width
