# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from cocotb_bus.scoreboard import Scoreboard as BaseScoreboard
from cocotb.result import TestFailure
from cocotb_bus.monitors import Monitor
import logging


class Scoreboard(BaseScoreboard):
    """
    Custom scoreboard for test of axis merger. Instead of checking if the received transactions
    are correct and in the correct order, this scoreboard only checks if they are correct,
    but ignores order.
    """

    def compare(self, got, exp, log, strict_type=True):
        if strict_type:
            if type(exp[0]) is not type(got):
                raise TestFailure("Received transaction of different type then expected.")

        if got not in exp:
            log.error(f"Expected one of: {exp}\n\nGot: {got}")
            raise TestFailure("Received unexpected transaction.")

        else:
            exp.remove(got)

    def add_interface(self, monitor, expected_output, compare_fn=None, reorder_depth=0, strict_type=True):
        self.expected[monitor] = expected_output

        if not isinstance(monitor, Monitor):
            raise TypeError("Expected monitor on the interface but got %s" %
                            (type(monitor).__qualname__))

        self.log.info("Created with reorder_depth %d" % reorder_depth)

        def check_received_transaction(transaction):
            """Called back by the monitor when a new transaction has been
            received."""

            if monitor.name:
                log_name = self.log.name + '.' + monitor.name
            else:
                log_name = self.log.name + '.' + type(monitor).__qualname__

            log = logging.getLogger(log_name)

            if len(expected_output) == 0:
                self.errors += 1
                log.error("Received a transaction but wasn't expecting "
                          "anything")
                log.info("Got: %s", transaction)
                if self._imm:
                    raise TestFailure("Received a transaction but wasn't "
                                      "expecting anything")
                return

            self.compare(transaction, expected_output, log, strict_type=strict_type)

        monitor.add_callback(check_received_transaction)
