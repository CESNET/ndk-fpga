# test_units.py: unit test of the unit conversion helpers
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

import pytest

from ofm.utils.units import convert_units


@pytest.mark.parametrize("value, in_units, expected", [
    (5e-15, "", (5.0, "f")),
    (2500, "f", (2.5, "p")),
    (0.5, "p", (500.0, "f")),
    (3e-12, "", (3.0, "p")),
    (4e3, "", (4.0, "k")),
])
def test_unit_is_chosen_from_the_value(value, in_units, expected):
    converted, units = convert_units(value, in_units)

    assert units == expected[1]
    assert converted == pytest.approx(expected[0])


def test_femto_units_convert_to_base_units():
    assert convert_units(7, "f", "")[0] == pytest.approx(7e-15)
