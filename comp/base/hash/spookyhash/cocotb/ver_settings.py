# SPDX-License-Identifier: BSD-3-Clause
# Copyright (C) 2025 CESNET z. s. p. o.
# Author(s): Ondrej Schwarz <ondrejschwarz@cesnet.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "KEY_WIDTH"  : "1528",
        "HASH_WIDTH" : "128",
        "META_WIDTH" : "32",
        "OUT_REG"    : "True",
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
    "hash_width_unaligned": {
        "KEY_WIDTH": "123"
    },
    "no_out_reg": {
        "OUT_REG": "False",
    }
}

combinations = [(), ("hash_width_8b"), ("hash_width_16b"), ("hash_width_32b"), ("hash_width_64b"),
                ("key_width_unaligned"), ("hash_width_unaligned"), ("no_out_reg")]

for i in range(1, 64):
    SETTINGS[f"key_width_{i}B"] = {"KEY_WIDTH": str(i*8)}
    combinations.append((f"key_width_{i}B",))

SETTINGS["_combinations_"] = tuple(combinations)
