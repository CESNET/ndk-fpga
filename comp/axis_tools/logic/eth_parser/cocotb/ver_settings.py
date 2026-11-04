# ver_settings.py
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    "default": {
        "AXI_TDATA_WIDTH": "512",
        "PKT_MTU":         "16384",
        "FIFO_DEPTH":      "64",
    },

    "bus_128": {
        "AXI_TDATA_WIDTH": "128",
    },

    "bus_256": {
        "AXI_TDATA_WIDTH": "256",
    },

    "bus_1024": {
        "AXI_TDATA_WIDTH": "1024",
    },

    "mtu_2k": {
        "PKT_MTU": "2048",
    },

    "_combinations_": (
        (),
        ("bus_128",),
        ("bus_256",),
        ("bus_1024",),
        ("bus_256", "mtu_2k"),
    ),
}
