############################################################
# timestamp_limiter.py: Timestamp Limiter component class
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
############################################################

import nfb


class TimestampLimiter(nfb.BaseComp):
    """Timestamp Limiter component class

    This class mediates the HW component address space and communication protocol.
    """

    # DevTree compatible string
    DT_COMPATIBLE = "cesnet,ofm,timestamp_limiter"

    # MI ADDRESS SPACE
    _RESET_REG  = 0x00
    _SEL_QUEUE_REG = 0x04
    _TOP_SPEED_REG = 0x08

    def __init__(self, **kwargs):
        """Constructor"""

        try:
            super().__init__(**kwargs)
            self._name = "Timestamp Limiter"
            if "index" in kwargs:
                self._name += " " + str(kwargs.get("index"))
        except Exception:
            print("Error while opening Timestamp Limiter component!")

    def print_cfg(self):
        """Print current configuration"""

        sel_queues = bin(self._comp.read32(self._SEL_QUEUE_REG))[2:]
        top_speed_en = self._comp.read32(self._TOP_SPEED_REG)

        if "1" not in sel_queues:
            msg_queues = "Warning: No queues selected for reset. The reset will have no effect."
        elif "0" not in sel_queues:
            msg_queues = "All queues selected for reset (default)"
        else:
            msg_queues = "Queues selected for reset: "
            first = True
            for i, q in enumerate(reversed(sel_queues)):
                if q == "1":
                    msg_queues += ("" if first else ",") + str(i)
                    first = False
            msg_queues += "\n{NOTE: The listed Queues (above) are values from a 32-bit register and may not correspond with the number of Queues in each Timestamp Limiter}"

        msg_speed = "Top speed: {}".format("enabled" if top_speed_en else "disabled")

        print("\"{0}\"\n{1}\n{2}".format(self._name, msg_queues, msg_speed))

    def configure(self, cfg):
        """Configure component"""

        try:
            self._comp.write32(self._SEL_QUEUE_REG, cfg["select_queue_bitmap"])
            self._comp.write32(self._TOP_SPEED_REG, cfg["top_speed_en"])
        except Exception:
            print("{}: Error while writing configuration!".format(self._name))
            # Reset all queues in the default state
            self._comp.write32(self._SEL_QUEUE_REG, 2**32 - 1)

    def reset(self):
        """Issue a reset for the selected queues"""

        self._comp.write32(self._RESET_REG, 1)

    def top_speed_en(enable, self):
        """Enable or disable top speed"""

        self._comp.write32(self._TOP_SPEED_REG, enable)
