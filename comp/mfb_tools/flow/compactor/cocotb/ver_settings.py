# ver_settings.py: generic-override sweep for MFB_COMPACTOR's cocotb testbench
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#
# Run with (from this directory, after `make cocotb-venv`):
#   python3 ../../../../../build/scripts/multi_ver/multi_ver_cocotb.py ver_settings.py
# or a single combination:
#   python3 ../../../../../build/scripts/multi_ver/multi_ver_cocotb.py ver_settings.py -s region_size_2
#
# The full cocotb_test.py suite runs unmodified (arbitrary, non-region-aligned
# item-granular frame sizes included) under every combination below, and META
# gets exercised whenever META_WIDTH>0, so this is the only place the
# non-default generic corners (REGION_SIZE>1, META_WIDTH>0, USE_PIPE=False,
# FLUSH_TIMEOUT=0, FWFT_MODE=False) get any coverage - `make` alone only
# ever elaborates the entity's own defaults (matching the R-Tile PCIe HIP
# reference instance).

SETTINGS = {
    "default": {
        "REGIONS"       : "4",
        "REGION_SIZE"   : "1",
        "BLOCK_SIZE"    : "8",
        "ITEM_WIDTH"    : "32",
        "META_WIDTH"    : "0",
        "FLUSH_TIMEOUT" : "8",
        "USE_PIPE"      : "True",
        "FWFT_MODE"     : "True",
    },
    "meta_width_8": {
        "META_WIDTH": "8",
    },
    "meta_width_32": {
        "META_WIDTH": "32",
    },
    "use_pipe_false": {
        "USE_PIPE": "False",
    },
    "fwft_mode_false": {
        "FWFT_MODE": "False",
    },
    "flush_timeout_0": {
        "FLUSH_TIMEOUT": "0",
    },
    "flush_timeout_1": {
        "FLUSH_TIMEOUT": "1",
    },
    "few_regions": {
        "REGIONS": "2",
    },
    "region_size_2": {
        "REGION_SIZE": "2",
    },
    "region_size_4": {
        "REGION_SIZE": "4",
    },
    "_combinations_": (
        (), # "default" alone, same as make with no GENERICS override
        ("meta_width_8",),
        ("meta_width_32",),
        ("use_pipe_false",),
        ("fwft_mode_false",),
        ("flush_timeout_0",),
        ("flush_timeout_1",),
        ("few_regions",),
        ("region_size_2",),
        ("region_size_4",),
        ("region_size_2", "meta_width_8"),
        ("region_size_2", "use_pipe_false"),
        ("region_size_4", "few_regions"),
        ("fwft_mode_false", "flush_timeout_0"),
    ),
}
