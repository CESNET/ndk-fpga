# signals.py: Reading DUT signals from the observers
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author: David Beneš <benes@dyna-nic.com>, 2026
#
# SPDX-License-Identifier: BSD-3-Clause

"""Helpers for reading DUT signals in the monitor and the AXI checker.

Both observers have to tell a resolved value from one that still carries X or Z,
because a handshake sampled on an undefined signal says nothing about the DUT.
Keeping the two helpers here means a change to how resolution is decided applies
to everything that observes the bridge.
"""

from typing import Any, Optional


def bit(signal: Any) -> bool:
    """True when the signal is a resolved '1'; X and Z read as False.

    A one-bit signal reads back as a Logic and a wider one as a LogicArray, so
    the comparison goes through str() rather than a method only one of them has.
    """
    return signal.value.is_resolvable and str(signal.value) == "1"


def uint(signal: Any) -> Optional[int]:
    """Signal as an unsigned int, or None when any bit is undefined."""
    return signal.value.to_unsigned() if signal.value.is_resolvable else None
