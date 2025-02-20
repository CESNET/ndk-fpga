# scoreboard.py: Custom scoreboard for MI Pipe Test
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <Ondrej.Schwarz@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

from cocotb_bus.scoreboard import Scoreboard as BaseScoreboard
from cocotbext.ofm.mi.transaction import MiTransaction
from cocotb.utils import hexdiffs
from cocotb.result import TestFailure


class Scoreboard(BaseScoreboard):
    """Custom scoreboard for MI Pipe Test"""

    def __init__(self, dut, reorder_depth=0, fail_immediately=True):
        super().__init__(dut, reorder_depth=reorder_depth, fail_immediately=fail_immediately)

    def compare(self, got: MiTransaction, exp: MiTransaction, log, strict_type=True):
        """Custom compare function for MI Pipe Test

        Args:
            got: object from MiTransaction class passed by the monitor
            exp: object from MiTransaction class passed by the test
            log: logging object
            strict_type: if type of the transaction should be compared
        """

        # Type comparison
        if strict_type and type(got) is not type(exp):
            self.errors += 1
            log.error("Received transaction type is different than expected")
            log.info("Received: %s but expected %s" %
                     (str(type(got)), str(type(exp))))
            if self._imm:
                raise TestFailure("Received transaction of wrong type. "
                                  "Set strict_type=False to avoid this.")
            return

        elif not strict_type:
            raise NotImplementedError("Non-strict type not implemented for MI Pipe Test.")

        # Comparing modeled and received values
        strgot, strexp = [], []

        if got.trans_type != exp.trans_type:
            return

        for i in ["addr", "data", ("be", "byte_enable")]:
            item, text = i if isinstance(i, tuple) else (i, i)
            if getattr(got, item) != getattr(exp, item):
                self.errors += 1
                strgot.append(f"{text}: {hex(getattr(got, item))}")
                strexp.append(f"{text}: {hex(getattr(exp, item))}")

        if self.errors > 0:
            log.error("Received transaction differed from expected output")
            log.info(f"Expected: {'; '.join(strexp)}")
            log.info(f"Received: {'; '.join(strgot)}")

            log.warning("Difference:\n%s" % hexdiffs('; '.join(strexp), '; '.join(strgot)))
            if self._imm:
                raise TestFailure("Received transaction differed from expected "
                                  "transaction")
        else:
            try:
                log.debug("Received expected transaction %d bytes" %
                          (len(got)))
                log.debug(repr(got))
            except Exception:
                pass
