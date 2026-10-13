# ver_settings.py: generic-override sweep for MFB_SWITCH_SIMPLE's cocotb testbench
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause
#
# Run with (from this directory, after `make cocotb-venv`):
#   python3 ../../../../../build/scripts/multi_ver/multi_ver_cocotb.py ver_settings.py
#
# Small FIFOs become full quickly. A deadlock between the outputs then appears
# within a short test.

SETTINGS = {
    "default": {
        "PORTS"        : "2",
        "REGIONS"      : "4",
        "REGION_SIZE"  : "8",
        "BLOCK_SIZE"   : "8",
        "ITEM_WIDTH"   : "8",
        "META_WIDTH"   : "8",
        "FIFO_DEPTH"   : "16",
        "PKT_SIZE_MAX" : "512",
    },
    "regions_1": {
        "REGIONS"      : "1",
        "FIFO_DEPTH"   : "32",
    },
    "ports_4": {
        "PORTS": "4",
    },
    "_combinations_": (
        (),  # "default" alone
        ("regions_1",),
        ("ports_4",),
    ),
}
