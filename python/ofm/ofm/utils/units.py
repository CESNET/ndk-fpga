# units.py: Utilities for unit conversions
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Ondřej Schwarz <Ondrej.Schwarz@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

decadic_conversions = {
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


def convert_units(value: float, in_units: str = "", out_units: str = None) -> (float, str):
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
    assert in_units in decadic_conversions.keys()
    assert out_units in decadic_conversions.keys() or out_units is None

    value = value * decadic_conversions[in_units]  # converting value to base units

    if out_units is None:
        if value == 0.0:
            out_units = list(decadic_conversions.keys())[0]
            return value, out_units

        for out_units in decadic_conversions:
            value_temp = value / decadic_conversions[out_units]

            if value_temp < 1000 and value_temp >= 1:
                value = value_temp
                break

    else:
        value = value / decadic_conversions[out_units]

    return value, out_units
