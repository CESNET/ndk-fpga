# units.py: Utilities for unit conversions
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <Ondrej.Schwarz@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

from typing import Tuple, Optional


decadic_conversions = {
    "f": 0.000_000_000_000_001,
    "p": 0.000_000_000_001,
    "n": 0.000_000_001,
    "u": 0.000_001,
    "m": 0.001,
    "" : 1,
    "k": 1000,
    "M": 1_000_000,
    "G": 1_000_000_000,
    "T": 1_000_000_000_000
}


def convert_units(value: float, in_units: str = "", out_units: Optional[str] = None) -> Tuple[float, str]:
    """
    Converts a value from one type of unit to another. If no out_units are passed,
    units are chosen automatically based on the value.

    Args:
        value: value to be converted.
        in_units: in which units is the passed value.
        out_units: to which units should the value be converted. If None is passed,
                   it's automatically chosen based on the value.

    Return:
        value: converted value.
        out_units: in which units the converted value is.
    """
    units = list(decadic_conversions.keys())
    assert in_units in units
    assert out_units in units or out_units is None

    value *= decadic_conversions[in_units]  # converting value to base units
    abs_value = abs(value)

    if out_units is None:
        out_units = "" if abs_value == 0.0 else units[0]
        for ou in units[1:]:
            if abs_value < decadic_conversions[ou]:
                break
            out_units = ou

    value /= decadic_conversions[out_units]
    return value, out_units
