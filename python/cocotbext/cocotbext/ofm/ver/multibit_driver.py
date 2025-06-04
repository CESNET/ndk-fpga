# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

import cocotb
from cocotb_bus.drivers import BitDriver
from cocotb.triggers import RisingEdge
from typing import Callable
from cocotb.clock import Clock
from random import randint


class Patterns:
    """
    Includes methods used with the MultiBitDriver as the 'pattern' argument.
    To be compatible with the driver the methods should accept at least
    two parameters, which are width of the signal that is set and the
    state of the driver, which is either 0 as off or 1 as on. Other
    parameters can be passed via the 'pattern_args' tuple, which is passed
    as *args. A string of ones and zeros representing a binary number shall
    be returned.
    """

    @staticmethod
    def all_at_once(signal_width: int, on_off: int, *args) -> str:
        return ('0' if on_off else '1') * signal_width

    @staticmethod
    def random(signal_width: int, *args) -> str:
        return "".join([str(randint(0, 1)) for _ in range(signal_width)])


class MultiBitDriver(BitDriver):
    """
    Extension of cocotb BitDriver capable of driving multiple bits instead of just one with
    configurable driving patterns.
    Useful for testing unstable ready and valid signals.

    Args:
        signal: the signal to be driven.
        clk: Clock object.
        generator: generator used to set the drivers states (on=1/off=0).
        pattern: function returning a value that is assigned to the signal.
        pattern_args: tuple of arguments passed to the pattern function.
    """

    def __init__(self, signal, clk: Clock, generator=None, pattern: Callable = Patterns.all_at_once, pattern_args: tuple = ()):
        self.__pattern = pattern
        self.__pattern_args = pattern_args
        super().__init__(signal, clk, generator)

    @cocotb.coroutine
    def _cr_twiddler(self, generator=None):
        if generator is None and self._generator is None:
            raise Exception("No generator provided!")
        if generator is not None:
            self._generator = generator

        edge = RisingEdge(self._clk)
        sig_width = len(self._signal)

        while True:
            on, off = next(self._generator)

            for e in range(2):
                val = self.__pattern(sig_width, e, *self.__pattern_args)

                self._signal.value = int(val, 2)

                for _ in range((off if e else on)):
                    yield edge
