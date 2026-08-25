############################################################
# rate_limiter.py: Rate Limiter component class
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Tomas Hak <xhakto01@vut.cz>
############################################################

import nfb
from math import ceil


class RateLimiter(nfb.BaseComp):
    """Rate Limiter component class

    This class mediates the HW component address space and communication protocol.

    Args:
        mfb_word_width: MFB bus word width in bits (default 512 for 100G, use 2048 for 400G).
        mfb_regions: Number of MFB regions (default 1 for 100G, use 4 for 400G).
        **kwargs: Additional arguments passed to nfb.BaseComp.
    """

    # DevTree compatible string
    DT_COMPATIBLE = "cesnet,ofm,rate_limiter"

    # MI ADDRESS SPACE
    _REG_STATUS    = 0x00
    _REG_SEC_LEN   = 0x04
    _REG_INT_LEN   = 0x08
    _REG_INT_CNT   = 0x0c
    _REG_FREQ      = 0x10
    _REG_SPEED_PTR = 0x14
    _REG_SPEED     = 0x18

    # STATUS REGISTER FLAGS
    _SR_IDLE_FLAG   = 0x01  # bit 0
    _SR_CONF_FLAG   = 0x02  # bit 1
    _SR_RUN_FLAG    = 0x04  # bit 2
    _SR_WR_AUX_FLAG = 0x08  # bit 3
    _SR_SHAPE_FLAG  = 0x10  # bit 4

    def __init__(self, mfb_word_width=512, mfb_regions=1, **kwargs):
        """Constructor

        Args:
            mfb_word_width: MFB bus word width in bits (100G: 512, 400G: 2048).
            mfb_regions: Number of MFB regions (100G: 1, 400G: 4).
            **kwargs: Arguments passed to nfb.BaseComp (dev, node, index, etc.).
        """

        try:
            super().__init__(**kwargs)
            self._name = "Rate Limiter"
            if "index" in kwargs:
                self._name += " " + str(kwargs.get("index"))
        except Exception:
            print("Error while opening Rate Limiter component!")

        self._mfb_word_width = mfb_word_width
        self._mfb_regions = mfb_regions

    def _fix_sec_len(self, orig_speed, sec_len, freq, min_speed):
        """Increase Section length when the speed of the Speed register would be below the limit"""

        if (sec_len < min_speed * freq / orig_speed):
            return int(min_speed * freq / orig_speed)
        return sec_len

    def _conv_Gbs2Bscn(self, speed, sec_len, freq):
        """Convert Gb/s to B/section"""

        min_speed = 1 + 3 * self._mfb_word_width / 8
        fixed_sec_len = self._fix_sec_len(speed * 125_000_000, sec_len, freq * 1_000_000, min_speed)

        self._comp.write32(self._REG_SEC_LEN, fixed_sec_len)

        ticks_per_sec    = freq * 1_000_000
        sections_per_sec = ticks_per_sec / fixed_sec_len
        bytes_per_sec    = speed * 125_000_000
        return int(ceil(bytes_per_sec / sections_per_sec))

    def _conv_Bscn2Gbs(self, speed, sec_len, freq):
        """Convert B/section to Gb/s"""

        ticks_per_sec    = freq * 1_000_000
        sections_per_sec = ticks_per_sec / sec_len
        bytes_per_sec    = speed * sections_per_sec
        return int(round(bytes_per_sec / 125_000_000))

    def _conv_Ps2Pscn(self, speed, sec_len, freq):
        """Convert pkts/s to pkts/section"""

        min_speed = 1 + self._mfb_regions
        fixed_sec_len = self._fix_sec_len(speed, sec_len, freq * 1_000_000, min_speed)

        self._comp.write32(self._REG_SEC_LEN, fixed_sec_len)

        ticks_per_sec    = freq * 1_000_000
        sections_per_sec = ticks_per_sec / fixed_sec_len
        return int(ceil(speed / sections_per_sec))

    def _conv_Pscn2Ps(self, speed, sec_len, freq):
        """Convert pkts/section to pkts/s"""

        ticks_per_sec    = freq * 1_000_000
        sections_per_sec = ticks_per_sec / sec_len
        return int(round(speed * sections_per_sec))

    def get_frequency(self):
        """Retrieve frequency in Hz"""

        return self._comp.read32(self._REG_FREQ) * 1_000_000

    def get_limit_type(self):
        """Retrieve type of limiting"""

        return self._comp.read32(self._REG_STATUS) & self._SR_SHAPE_FLAG

    def print_cfg(self):
        """Print current configuration"""

        try:
            status     = self._comp.read32(self._REG_STATUS)
            sec_len    = self._comp.read32(self._REG_SEC_LEN)
            max_speeds = self._comp.read32(self._REG_INT_CNT)
            frequency  = self._comp.read32(self._REG_FREQ)

            status_s     = "Idle"
            if (status & self._SR_CONF_FLAG):
                status_s = "Configuration"
            elif (status & self._SR_RUN_FLAG):
                status_s = "Running traffic shaping"

            limit_s      = "Gb/s"
            limit_alt_s  = "Bytes/section"
            if (status & self._SR_SHAPE_FLAG):
                limit_s     = "pkts/s"
                limit_alt_s = "pkts/section"

            output_speeds = []
            alt_speeds    = []
            for i in range(max_speeds):
                self._comp.write32(self._REG_SPEED_PTR, i)
                speed = self._comp.read32(self._REG_SPEED)
                valid = speed & (1 << 31)
                speed &= (1 << 31) - 1
                if (valid == 0):
                    break
                if (status & self._SR_SHAPE_FLAG):
                    output_speeds.append(self._conv_Pscn2Ps(speed, sec_len, frequency))
                else:
                    output_speeds.append(self._conv_Bscn2Gbs(speed, sec_len, frequency))
                alt_speeds.append(speed)

            print("\"{}\"".format(self._name))
            print("Status:          {0:08x} ({1})".format(status, status_s))
            print("Section length:  {} clock cycles".format(sec_len))
            print("Interval length: {} sections".format(self._comp.read32(self._REG_INT_LEN)))
            print("Interval count:  {} intervals".format(max_speeds))
            print("Frequency:       {} MHz".format(frequency))
            print("Output speed:    {0} {1}".format(output_speeds, limit_s))
            print("Output speed:    {0} {1}".format(alt_speeds, limit_alt_s))
        except Exception:
            print("{}: Error while reading configuration!".format(self._name))

    def configure(self, cfg):
        """Configure component"""

        try:
            frequency  = self._comp.read32(self._REG_FREQ)
            if (cfg["section_length"] >= frequency * 1_000_000):
                print("{}: Error - Section too long!".format(self._name))
                return

            self._comp.write32(self._REG_STATUS, self._SR_CONF_FLAG)
            self._comp.write32(self._REG_SEC_LEN, cfg["section_length"])
            self._comp.write32(self._REG_INT_LEN, cfg["interval_length"])

            max_speeds = self._comp.read32(self._REG_INT_CNT)
            available  = max_speeds
            for i, speed in enumerate(cfg["output_speed"]):
                if (available == 0):
                    print("{0}: Insufficient number of speed regs in the design ({1})! Ignoring speeds over the limit...".format(self._name, max_speeds))
                    break
                self._comp.write32(self._REG_SPEED_PTR, i)
                if (cfg["limit_packets"]):
                    self._comp.write32(self._REG_SPEED, self._conv_Ps2Pscn(speed, cfg["section_length"], frequency))
                else:
                    self._comp.write32(self._REG_SPEED, self._conv_Gbs2Bscn(speed, cfg["section_length"], frequency))
                available -= 1
        except Exception:
            print("{}: Error while writing configuration!".format(self._name))
        finally:
            auxiliary_flags = 0
            if (cfg["limit_packets"]):
                auxiliary_flags |= self._SR_SHAPE_FLAG
            self._comp.write32(self._REG_STATUS, (self._SR_WR_AUX_FLAG | auxiliary_flags))

    def start_shaping(self):
        """Start traffic shaping"""

        self._comp.write32(self._REG_STATUS, self._SR_RUN_FLAG)

    def stop_shaping(self):
        """Stop traffic shaping"""

        self._comp.write32(self._REG_STATUS, 0)
