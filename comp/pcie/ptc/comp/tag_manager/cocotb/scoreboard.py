# scoreboard.py: Collector of the failed checks of the tag manager model
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import cocotb


class Scoreboard:
    """
    Collects the assertion failures raised by the checks of the reference model.

    The model checks rules that have to hold while the traffic runs, see model.py.
    A failed check is logged and counted here. The test does not compare whole
    transactions against a queue of expected ones.
    """

    def __init__(self):
        self.errors: list[str] = []

    def check(self, fn, *args, **kwargs) -> None:
        """Run fn(*args, **kwargs) and record an AssertionError instead of stopping the test."""
        try:
            fn(*args, **kwargs)
        except AssertionError as e:
            msg = str(e)
            cocotb.log.error(msg)
            self.errors.append(msg)

    def raise_if_errors(self) -> None:
        if self.errors:
            raise AssertionError(f"{len(self.errors)} failed check(s):\n" + "\n".join(self.errors))
