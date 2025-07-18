# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#


def mask_value(val: int, mask: int) -> int:
    """Return only the value specified by the mask.

    Useful when, for example, reading data from a multi-value register.

    How it works:
    After masking by the AND operator, the masked bits that are now 0 are excluded from the
    number by shifting.

    Args:
    val: The number that will be masked by the `mask`.
    mask: The mask that will be applied to the `val`.

    Returns:
    A number with bits cut off from the front and/or back according to the provided mask from the original value.
    """
    # Get only the mask's first '1' bit:
    # AND the mask's twos complement with the original mask.
    first_mask_bit = mask & -mask
    # Get the bit's position:
    # obtained by using the bit_length() function, which returns the number of bits that are
    # necessary for the binary representation of this number.
    first_mask_bit_pos = first_mask_bit.bit_length()
    # The shift size must be one less than the bit's position.
    shift_size = first_mask_bit_pos - 1
    return (val & mask) >> shift_size


def apply_value(base: int, part: int, mask: int) -> int:
    """Replace a part in the original value indicated by the mask with a new value.

    Useful when, for example, writing data to a multi-value register.

    How it works:
    The new part is shifted to the place specified by the mask and ORed with the masked value of
    the base value.

    Args:
    base: The original (base) number.
    part: The number that will be replace a part in the original number.
    mask: Masks the base value where the new value will replace the original one.

    Returns:
    the original number with one of its parts replaced with the new value.
    """
    # Get only the mask's first '1' bit:
    # AND the mask's twos complement with the original mask.
    first_mask_bit = mask & -mask
    # Get the bit's position:
    # obtained by using the bit_length() function, which returns the number of bits that are
    # necessary for the binary representation of this number.
    shift_size = first_mask_bit.bit_length()

    shf_part = part << shift_size
    if shf_part > mask:
        raise ValueError(f"The part ({part} is too large or the mask ({mask} is too small!))")
    return (base & ~mask) | shf_part
