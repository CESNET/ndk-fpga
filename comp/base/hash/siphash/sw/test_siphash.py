# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

import pytest
import siphash
from parse import parse
import subprocess
from random import randint, randbytes

NUM_ITERATIONS = 1000

# creating keys and messages
test_data = list()

for _ in range(NUM_ITERATIONS):
    message = randbytes(randint(1, 192))
    key = randbytes(16)
    test_data.append((key, message))


@pytest.mark.parametrize("key, message", test_data)
def test_siphash(key: bytes, message: bytes):
    # running test and collecting results
    test = subprocess.run(["./test", "-m", message.hex(), "-k", key.hex()], capture_output=True, text=True)
    pattern = "SipHash::Hash_2_4 = {}\nSipHash::Hash_4_8 = {}\nSipHash::Hash_2_4_128 = {}\nSipHash::Hash_4_8_128 = {}\nHalfSipHash::Hash_2_4 = {}\nHalfSipHash::Hash_4_8 = {}\nHalfSipHash::Hash_2_4_64 = {}\nHalfSipHash::Hash_4_8_64 = {}\n"
    results = parse(pattern, test.stdout)

    # evaluating results
    assert f"0x{results[0]}" == hex(int.from_bytes(siphash.siphash_64(key, message, 2, 4), "little"))
    assert f"0x{results[1]}" == hex(int.from_bytes(siphash.siphash_64(key, message, 4, 8), "little"))
    assert f"0x{results[2]}" == hex(int.from_bytes(siphash.siphash_128(key, message, 2, 4), "little"))
    assert f"0x{results[3]}" == hex(int.from_bytes(siphash.siphash_128(key, message, 4, 8), "little"))
    assert f"0x{results[4]}" == hex(int.from_bytes(siphash.half_siphash_32(key[:8], message, 2, 4), "little"))
    assert f"0x{results[5]}" == hex(int.from_bytes(siphash.half_siphash_32(key[:8], message, 4, 8), "little"))
    assert f"0x{results[6]}" == hex(int.from_bytes(siphash.half_siphash_64(key[:8], message, 2, 4), "little"))
    assert f"0x{results[7]}" == hex(int.from_bytes(siphash.half_siphash_64(key[:8], message, 4, 8), "little"))
