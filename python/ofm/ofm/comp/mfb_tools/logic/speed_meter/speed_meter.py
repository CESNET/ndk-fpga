# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Tomas Hak <xhakto01@vut.cz>
#            Daniel Kondys <kondys@cesnet.cz>

from time import sleep
from typing import Optional, Tuple

import nfb


class SpeedMeter(nfb.BaseComp):
    """Speed Meter component class

    This class mediates the HW component address space and communication protocol.

    Set `lightweight=True` to use only the 4 basic registers: _REG_TICKS, _REG_STATUS, _REG_BYTES, and _REG_CLEAR.
    """

    # DevTree compatible string
    DT_COMPATIBLE = "cesnet,ofm,speed_meter"

    # MI ADDRESS SPACE
    _REG_TICKS  = 0x00
    _REG_STATUS = 0x04
    _REG_BYTES  = 0x08
    _REG_CLEAR  = 0x0C
    _REG_SOFS   = 0x10
    _REG_EOFS   = 0x14
    _REG_FREQ   = 0x18

    # STATUS REGISTER FIELDS
    _SR_DONE_FLAG = 0x00

    def __init__(self, lightweight: bool = False, **kwargs):
        """Constructor"""

        super().__init__(**kwargs)
        self._name = "Speed Meter"
        if "index" in kwargs:
            self._name += " " + str(kwargs.get("index"))

        self._lightweight = lightweight

    def test_complete(self) -> bool:
        """Same as the `done` property - for backward compatibility."""
        return self.done

    def get_frequency(self) -> int:
        """Same as the `frequency` property - for backward compatibility."""
        return self.frequency

    def get_data(self) -> Tuple[int, int, int | None, int | None]:
        """Same as the `data` property - for backward compatibility."""
        return self.data

    @property
    def done(self) -> bool:
        """Check if speed measurement is complete."""
        return self._comp.get_bit(self._REG_STATUS, self._SR_DONE_FLAG)

    @property
    def frequency(self) -> int:
        """Retrieve frequency in Hz."""
        if self._lightweight:
            raise ValueError("Cannot read frequency from FW when in the Lightweight mode!")
        return self._comp.read32(self._REG_FREQ) * 1_000_000

    @property
    def items(self) -> int:
        """Read the number of accumulated bytes."""
        return self._comp.read32(self._REG_BYTES)

    @property
    def ticks(self) -> int:
        """Read the number of passed clock cycles (ticks)."""
        return self._comp.read32(self._REG_TICKS)

    @property
    def sofs(self) -> int:
        """Read the number of accumulated frames started (MFB SOFs)."""
        if self._lightweight:
            raise ValueError("Cannot read SOFs from FW when in the Lightweight mode!")
        return self._comp.read32(self._REG_SOFS)

    @property
    def eofs(self) -> int:
        """Read the number of accumulated frames ended (MFB EOFs)."""
        if self._lightweight:
            raise ValueError("Cannot read EOFs from FW when in the Lightweight mode!")
        return self._comp.read32(self._REG_EOFS)

    @property
    def data(self) -> Tuple[int, int, int | None, int | None]:
        """Read the number of accumulated bytes, ticks, and potentionally SOFs and EOFs."""
        if self._lightweight:
            return self.ticks, self.items, None, None
        else:
            return self.ticks, self.items, self.sofs, self.eofs

    def measure(self, to: float = 0.1, f: Optional[int] = 2*10**8) -> Tuple[float, float | None]:
        """Retrieve Speed meter's data and compute speed in [bps], potentionally also in [pps].

        Args:
            to: Timeout in [s]. The measurement is stopped if no data pass through in 10 timeouts.
            f: Frequency of the Clock signal the SpeedMeter is running on in [Hz].
               Set `None` to read from FW (not possible when the SM is in the Lightweight mode).

        Returns:
            A tuple of measured speed in [bps] and [pps] ([bps] and None in Lightweight mode).
        """
        if f is None:
            try:
                f = self.frequency
            except ValueError:
                raise

        cnt = 0
        while self.ticks == 0:
            sleep(to)
            cnt += 1
            if cnt < 10:
                continue
            return (0.0, None) if self._lightweight else (0.0, 0.0)

        while not self.done:
            sleep(to)
            continue

        # Number of accum. bits / (secs per clock clock cycle * the number of passed clock cycles)
        bps = self.items * 8 / ((1/f) * self.ticks)
        if not self._lightweight:
            pps = self.sofs / ((1/f) * self.ticks) # self.eofs could be used just as well

        return (bps, None) if self._lightweight else (bps, pps)

    def get_speed(self) -> Tuple[float, float]:
        """Retrieve speed both in b/s and in pkt/s."""

        ticks = self._comp.read32(self._REG_TICKS)
        if ticks != 0:
            while not self._comp.get_bit(self._REG_STATUS, self._SR_DONE_FLAG):
                continue
            ticks      = self._comp.read32(self._REG_TICKS)
            frequency  = self._comp.read32(self._REG_FREQ) * 1_000_000
            bps_speed  = float(frequency) / ticks * self._comp.read32(self._REG_BYTES)
            pkts_speed = float(frequency) / ticks * self._comp.read32(self._REG_SOFS)
            return bps_speed * 8, pkts_speed
        else:
            return 0, 0

    def clear_data(self):
        """Reset measurement statistics."""
        self._comp.write32(self._REG_CLEAR, 0x1)
