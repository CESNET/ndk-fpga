# ver_settings.py
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): Vladislav Valek <valekv@cesnet.cz>

# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    "default" : { # The default setting of verification
        "DATA_WIDTH"            : "16",
        "ITEMS"                 : "16",
        "FAKE_FIFO"             : "0",
    },

    "SIZE_SMALL" : {
        "DATA_WIDTH" : "2",
        "ITEMS"      : "1",
    },
    "SIZE_BIG" : {
        "DATA_WIDTH" : "256",
        "ITEMS"      : "1125",
    },
    "SIZE_AVERAGE" : {
        "DATA_WIDTH" : "64",
        "ITEMS"      : "20",
    },

    "_combinations_" : (
        (               ),
        ("SIZE_SMALL",  ),
        ("SIZE_BIG",    ),
        ("SIZE_AVERAGE",),
    ),
}
