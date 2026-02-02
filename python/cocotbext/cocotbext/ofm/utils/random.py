# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

from random import randint
from random import choice as randchoice


def randint_recursive(min_bits: int, max_bits: int, max_final_bit_range: int = 8):
    """
    Generates random integer of bit length in the passed range with better
    bit legth spread then the standart random.randint function.

    In every iteration the (min_bits, max_bits) range is split in half and one
    of the the two new intervals is randomly chosen and passed to randint_recursive
    again until the max_final_bit_range is reached.

    Args:
        min_bits: minimum bit legth of the generated number.
        max_bits: maximum bit length of the generated number.
        max_final_bit_range: the maximum length of bit range that shouldn't be
            split anymore and the final integer is generated from this range.
    """

    if max_bits - min_bits <= max_final_bit_range:
        return randint(2**min_bits-1, 2**max_bits-1)

    mid_bits = min_bits + ((max_bits - min_bits) // 2)
    interval = randchoice([(min_bits, mid_bits), (mid_bits, max_bits)])
    return randint_recursive(*interval, max_final_bit_range)
