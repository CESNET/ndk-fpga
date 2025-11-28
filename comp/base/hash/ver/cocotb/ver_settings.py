# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

SETTINGS = {
    # hash settings
    "default" : { # The default setting of verification
        "KEY_WIDTH"     : "1528",
        "HASH_WIDTH"    : "128",
        "META_WIDTH"    : "32",
        "OUT_REG"       : "True",
        "HASH_FUNCTION" : "SPOOKYHASH",
    },
    "hash_width_8b": {
        "HASH_WIDTH": "8"
    },
    "hash_width_16b": {
        "HASH_WIDTH": "16"
    },
    "hash_width_32b": {
        "HASH_WIDTH": "32"
    },
    "hash_width_64b": {
        "HASH_WIDTH": "64"
    },
    "key_width_unaligned": {
        "KEY_WIDTH": "1523"
    },
    "hash_width_unaligned_128": {
        "KEY_WIDTH": "123"
    },
    "hash_width_unaligned_64": {
        "KEY_WIDTH": "61"
    },
    "meta_width_64b": {
        "META_WIDTH": "64"
    },
    "no_out_reg": {
        "OUT_REG": "False",
    },

    # hash function select
    "function_spookyhash": {
        "HASH_FUNCTION": "SPOOKYHASH",
    },
    "function_siphash_2_4": {
        "HASH_FUNCTION": "SIPHASH_2_4",
    },
    "function_siphash_4_8": {
        "HASH_FUNCTION": "SIPHASH_4_8",
    },
    "function_halfsiphash_2_4": {
        "HASH_FUNCTION": "HALFSIPHASH_2_4",
    },
    "function_halfsiphash_4_8": {
        "HASH_FUNCTION": "HALFSIPHASH_4_8",
    },
}

options_128 = [(), ("hash_width_8b",), ("hash_width_16b",), ("hash_width_32b",), ("hash_width_64b",),
               ("key_width_unaligned",), ("hash_width_unaligned_128",), ("meta_width_64b",), ("no_out_reg",)]

options_64  = [("hash_width_8b",), ("hash_width_16b",), ("hash_width_32b",), ("hash_width_64b",),
               ("key_width_unaligned", "hash_width_64b",), ("hash_width_unaligned_64",),
               ("meta_width_64b", "hash_width_64b",), ("no_out_reg", "hash_width_64b",)]

functions_128 = ["function_spookyhash", "function_siphash_2_4", "function_siphash_4_8"]
functions_64  = ["function_halfsiphash_2_4", "function_halfsiphash_4_8"]

for i in range(1, 64):
    SETTINGS[f"key_width_{i}B"] = {"KEY_WIDTH": str(i*8)}
    options_128.append((f"key_width_{i}B",))
    options_64.append((f"key_width_{i}B", "hash_width_64b",))

combinations = []

for function in functions_128:
    for option in options_128:
        combinations.append((function, *option))

for function in functions_64:
    for option in options_64:
        combinations.append((function, *option))

SETTINGS["_combinations_"] = tuple(combinations)
