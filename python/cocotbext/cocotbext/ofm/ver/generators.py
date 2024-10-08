# generators.py: Generators for cocotb
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

import random


def random_byte():
    """
    Random byte generator
    """
    while True:
        yield random.randrange(256)


def random_bytes(bytes_count: int, generator):
    """
    Generate N random bytes from *generator*
    """
    return bytes(next(generator) for i in range(bytes_count))


def random_packets(min_size=4, max_size=64, count=10):
    """
    Generate N random packets with random length of bytes in min/max range
    """
    for i in range(count):
        yield random_bytes(random.randint(min_size, max_size), random_byte())
