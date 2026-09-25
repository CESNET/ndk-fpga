# scoreboard.py: Comparison of Avalon-MM requests against the AXI transactions
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author: David Beneš <benes@dyna-nic.com>, 2026
#
# SPDX-License-Identifier: BSD-3-Clause

"""Comparison of what the Avalon-MM master asked for against what the bridge did.

Write path: every word accepted on the Avalon-MM interface has to appear on the
AXI W channel, in the same order, at the byte address derived from the
Avalon-MM word address. Comparing the two streams directly catches lost,
duplicated and misplaced beats, which a read-back through the same bridge cannot
do because a wrong address cancels itself out.

Read path: every word returned on the Avalon-MM interface is compared against
the contents the reference model held when that read request was accepted, so
that a later write to the same word cannot change what the read owed.
"""

from typing import Optional

from cocotbext.ofm.utils.hex_formatter import format_bytes

from axi_checker import WriteBeat
from monitor import AmmWriteBeat

# how many differing beats are printed before the report is truncated
MAX_REPORTED_MISMATCHES = 5


def _beat_repr(address: Optional[int], data: bytes) -> str:
    location = "unknown address" if address is None else f"{address:#x}"
    return f"{location}\n{format_bytes(data, label='  data')}"


class Scoreboard:
    def __init__(self) -> None:
        self.errors: list[str] = []

    def check_write_path(self, expected: list[AmmWriteBeat], observed: list[WriteBeat]) -> None:
        if len(expected) != len(observed):
            self.errors.append(f"the bridge put {len(observed)} write beats on the AXI bus, but the Avalon-MM master handed it {len(expected)} words")

        mismatches = 0

        for index, (exp, obs) in enumerate(zip(expected, observed)):
            if exp.byte_address == obs.address and exp.data == obs.data:
                continue

            mismatches += 1
            if mismatches <= MAX_REPORTED_MISMATCHES:
                self.errors.append(
                    f"write beat {index} (Avalon-MM word {exp.word_address:#x}) does not match\n"
                    f"  expected at {_beat_repr(exp.byte_address, exp.data)}\n"
                    f"  observed at {_beat_repr(obs.address, obs.data)}")

        if mismatches > MAX_REPORTED_MISMATCHES:
            self.errors.append(f"... and {mismatches - MAX_REPORTED_MISMATCHES} further mismatching write beats")

    def check_read_path(self, expected_words: list[int], expected_data: list[bytes], received: list[bytes]) -> None:
        if len(expected_words) != len(received):
            self.errors.append(f"the bridge returned {len(received)} read words, but the accepted read requests asked for {len(expected_words)}")

        mismatches = 0

        for index, (word_address, reference, data) in enumerate(zip(expected_words, expected_data, received)):
            if reference == data:
                continue

            mismatches += 1
            if mismatches <= MAX_REPORTED_MISMATCHES:
                self.errors.append(
                    f"read word {index} (Avalon-MM word {word_address:#x}) does not match\n"
                    f"{format_bytes(reference, label='  expected')}\n"
                    f"{format_bytes(data, label='  received')}")

        if mismatches > MAX_REPORTED_MISMATCHES:
            self.errors.append(f"... and {mismatches - MAX_REPORTED_MISMATCHES} further mismatching read words")

    def report(self, checker_summary: str, violation_count: int) -> None:
        if not self.errors and not violation_count:
            return

        lines = []

        if violation_count:
            lines.append(f"{violation_count} AXI protocol violation(s):\n{checker_summary}")

        lines.extend(self.errors)

        raise AssertionError("\n\n".join(lines))
