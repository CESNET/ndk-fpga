############################################################
# speed_meter.py: Speed Meter component class
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Tomas Hak <xhakto01@vut.cz>
############################################################

import nfb


class SpeedMeter(nfb.BaseComp):
    """Speed Meter component class

    This class mediates the HW component address space and communication protocol.
    """

    # DevTree compatible string
    DT_COMPATIBLE = "cesnet,ofm,speed_meter"

    # MI ADDRESS SPACE
    _REG_TICKS  = 0x00
    _REG_STATUS = 0x04
    _REG_BYTES  = 0x08
    _REG_CLEAR  = 0x0c
    _REG_SOFS   = 0x10
    _REG_EOFS   = 0x14
    _REG_FREQ   = 0x18

    # STATUS REGISTER FIELDS
    _SR_DONE_FLAG = 0x00

    def __init__(self, **kwargs):
        """Constructor"""

        try:
            super().__init__(**kwargs)
            self._name = "Speed Meter"
            if "index" in kwargs:
                self._name += " " + str(kwargs.get("index"))
        except Exception:
            print("Error while opening Speed Meter component!")

    def test_complete(self):
        """Check if speed measurement is complete"""

        return self._comp.get_bit(self._REG_STATUS, self._SR_DONE_FLAG)

    def get_frequency(self):
        """Retrieve frequency in Hz"""

        return self._comp.read32(self._REG_FREQ) * 1_000_000

    def get_data(self):
        """Retrieve measured data"""

        return self._comp.read32(self._REG_BYTES), self._comp.read32(self._REG_SOFS), self._comp.read32(self._REG_EOFS), self._comp.read32(self._REG_TICKS)

    def get_speed(self):
        """Retrieve speed both in b/s and in pkt/s"""

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
        """Reset measurement statistics"""

        self._comp.write32(self._REG_CLEAR, 0x1)
