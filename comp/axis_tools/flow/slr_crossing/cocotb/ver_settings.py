# ver_settings.py
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    "default": {
        "TDATA_WIDTH":   "512",
        "TUSER_WIDTH":   "16",
        "USE_OUTREG":    "True",
        "FAKE_CROSSING": "False",
    },

    "bus_64": {
        "TDATA_WIDTH": "64",
    },

    "no_outreg": {
        "USE_OUTREG": "False",
    },

    "fake": {
        "FAKE_CROSSING": "True",
    },

    "_combinations_": (
        (),
        ("bus_64",),
        ("no_outreg",),
        ("no_outreg", "bus_64"),
        ("fake",),
    ),
}
