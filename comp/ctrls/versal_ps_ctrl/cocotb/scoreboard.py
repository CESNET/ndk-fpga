# scoreboard.py: Scoreboard of the VERSAL_PS_CTRL verification
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2026
#
# SPDX-License-Identifier: BSD-3-Clause

from typing import Any, Sequence


class Scoreboard:
    """Collects mismatches of all comparisons and reports them at once."""

    MAX_REPORTED = 10

    def __init__(self) -> None:
        self.errors: list[str] = []
        self.compared = 0

    def compare_lists(self, title: str, expected: Sequence[Any], actual: Sequence[Any]) -> None:
        """Compares two ordered streams item by item and records every difference."""
        mismatches = []

        for index in range(max(len(expected), len(actual))):
            exp = expected[index] if index < len(expected) else "<missing>"
            act = actual[index] if index < len(actual) else "<missing>"
            if exp != act:
                mismatches.append(f"  #{index:<5} expected {exp}\n         actual   {act}")

        self.compared += len(expected)

        if len(expected) != len(actual):
            self.errors.append(f"{title}: expected {len(expected)} items, got {len(actual)}")

        if mismatches:
            shown = "\n".join(mismatches[:self.MAX_REPORTED])
            more = f"\n  ... {len(mismatches) - self.MAX_REPORTED} more" if len(mismatches) > self.MAX_REPORTED else ""
            self.errors.append(f"{title}: {len(mismatches)} mismatches\n{shown}{more}")

    def check(self, condition: bool, message: str) -> None:
        if not condition:
            self.errors.append(message)

    def add_errors(self, title: str, errors: Sequence[str], total: int = 0) -> None:
        if errors:
            count = max(total, len(errors))
            self.errors.append(f"{title}: {count} violations\n  " + "\n  ".join(errors[:self.MAX_REPORTED]))

    def result(self) -> None:
        if self.errors:
            raise AssertionError("Verification failed:\n" + "\n".join(self.errors))
