# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#

from typing import Tuple, List


def concat(values: List[Tuple[int, int]]) -> int:
    """Concatenate the given values in order from the first (index 0) to the last.

    Args:
    values: A list where each item is a tuple (value, bit-width).

    Returns:
    A single integer composed of the "values" from the tuples in the input list.
    """
    vector = 0
    for val, width in reversed(values):
        # 1. Shifting
        vector <<= width
        # 2. Masking and concatenating
        vector |= val & (2**width - 1)
    return vector

def deconcat(vec: int, widths: List[int]) -> List[int]:
    """Splits the input integer into parts according to the given list of bit widths.

    Args:
    vec: The input vector that will be split (deconcatenated) into parts.
    widths:

    Returns:
    A list of parts of the input vector that have been split according to the given list of widths.
    """
    parts = []
    for width in widths:
        # 1. Masking
        parts.append(vec & (2**width - 1))
        # 2. Shifting
        vec >>= width
    return parts
