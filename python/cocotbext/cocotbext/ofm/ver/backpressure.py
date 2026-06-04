# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# Backpressure utilities for cocotb verification.
#
# Provides configurable backpressure generation for handshake-based bus interfaces.
# Can be used either as a standalone coroutine driving a ready signal directly,
# or as a generator compatible with cocotb BitDriver / MultiBitDriver.

import random
from dataclasses import dataclass
from typing import Optional, Tuple

from cocotb.triggers import ClockCycles


@dataclass
class BackpressureConfig:
    """Configuration for backpressure generation.

    Backpressure is applied by randomly deasserting a ready signal for bursts
    of clock cycles. The behavior is controlled by two parameters:

    - ``low_prob``: probability of the ready signal being driven low.
    - ``min_hold`` / ``max_hold``: range of clock cycles for which the
      ready value is held before a new random decision is made.

    Attributes:
        min_hold: Minimum number of clock cycles to hold the current ready
            value before re-evaluating.
        max_hold: Maximum number of clock cycles to hold the current ready
            value before re-evaluating.
        low_prob: Probability (0.0–1.0) that ready will be driven low.
    """

    min_hold: int = 1
    max_hold: int = 5
    low_prob: float = 0.3


async def apply_backpressure(
    signal,
    clock,
    cfg: Optional[BackpressureConfig] = None,
) -> None:
    """Drive a ready signal with random backpressure.

    This coroutine runs indefinitely (typically started via
    ``cocotb.start_soon``) and toggles the target signal between ``1`` and
    ``0`` according to the supplied configuration.

    Args:
        signal: The HDL signal to drive (e.g. ``dut.TX_AXI_TREADY``).
        clock: The cocotb clock signal associated with the interface.
        cfg: Backpressure configuration. If ``None``, a default instance
            (``BackpressureConfig()``) is used.
    """
    cfg = cfg or BackpressureConfig()

    while True:
        hold_cycles = random.randint(cfg.min_hold, cfg.max_hold)
        signal.value = 0 if random.random() < cfg.low_prob else 1
        await ClockCycles(clock, hold_cycles)


class BackpressureGenerator:
    """Generator compatible with :class:`cocotb_bus.drivers.BitDriver`.

    Produces ``(on, off)`` tuples where ``on`` is the number of cycles the
    signal stays at ``1`` (ready asserted) and ``off`` is the number of
    cycles the signal stays at ``0`` (ready deasserted / backpressure).
    These tuples match the format expected by :meth:`BitDriver.start`.

    Example::

        from cocotb_bus.drivers import BitDriver
        from cocotbext.ofm.ver.backpressure import BackpressureGenerator, BackpressureConfig

        gen = BackpressureGenerator(BackpressureConfig(1, 5, 0.5))
        bp = BitDriver(dut.TX_DST_RDY, dut.CLK)
        bp.start(gen)
    """

    def __init__(self, cfg: Optional[BackpressureConfig] = None) -> None:
        """Initialize the generator.

        Args:
            cfg: Backpressure configuration. If ``None``, a default instance
                (``BackpressureConfig()``) is used.
        """
        self.cfg = cfg or BackpressureConfig()

    def __iter__(self):
        return self

    def __next__(self) -> Tuple[int, int]:
        """Return the next ``(on, off)`` tuple for BitDriver.

        ``on``  = cycles with signal = 1 (ready asserted).
        ``off`` = cycles with signal = 0 (ready deasserted / backpressure).
        """
        cycles = random.randint(self.cfg.min_hold, self.cfg.max_hold)
        if random.random() < self.cfg.low_prob:
            return 0, cycles  # ready=0 for ``cycles``
        return cycles, 0    # ready=1 for ``cycles``
