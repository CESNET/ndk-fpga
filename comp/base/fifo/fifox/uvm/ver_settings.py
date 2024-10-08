# ver_settings.py
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    "default" : { # The default setting of verification
        "DATA_WIDTH"            : "16",
        "ITEMS"                 : "16",
        "RAM_TYPE"              : "\\\"AUTO\\\"",
        "DEVICE"                : "\\\"ULTRASCALE\\\"",
        "ALMOST_FULL_OFFSET"    : "0",
        "ALMOST_EMPTY_OFFSET"   : "0",
        "FAKE_FIFO"             : "0",
        "MIN_TRANSACTION_COUNT" : "4000",
        "MAX_TRANSACTION_COUNT" : "5000",
    },

    "DEVICE_7SERIES" : {
        "DEVICE" : "\\\"7SERIES\\\"",
    },
    "DEVICE_ARRIA10" : {
        "DEVICE" : "\\\"ARRIA10\\\"",
    },
    "DEVICE_STRATIX10" : {
        "DEVICE" : "\\\"STRATIX10\\\"",
    },
    "DEVICE_AGILEX" : {
        "DEVICE" : "\\\"AGILEX\\\"",
    },

    "ALMOST_FULL_OFFSET_5" : {
        "ALMOST_FULL_OFFSET" : "5",
    },
    "ALMOST_EMPTY_OFFSET_5" : {
        "ALMOST_EMPTY_OFFSET" : "5",
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
    "RAM_LUT" : {
        "RAM_TYPE"  : "\\\"LUT\\\"",
    },
    "RAM_BRAM" : {
        "RAM_TYPE"  : "\\\"BRAM\\\"",
    },
    "RAM_URAM" : {
        "RAM_TYPE"  : "\\\"URAM\\\"",
    },
    "RAM_SHIFT" : {
        "RAM_TYPE"  : "\\\"SHIFT\\\"",
    },


    "_combinations_" : (
        # '()' works the same as '("default",)'. "default" is applied in every combination

        (),

        ("SIZE_SMALL",   "DEVICE_7SERIES",),
        ("SIZE_BIG",     "DEVICE_ARRIA10",   "ALMOST_FULL_OFFSET_5", ),
        ("SIZE_AVERAGE", "DEVICE_STRATIX10", "ALMOST_EMPTY_OFFSET_5",),

        ("SIZE_AVERAGE", "DEVICE_AGILEX", "ALMOST_FULL_OFFSET_5", "ALMOST_EMPTY_OFFSET_5",),

        ("SIZE_BIG",),

        ("default", "RAM_LUT",),
        ("default", "RAM_BRAM",),
        ("default", "RAM_SHIFT",),
        #only for ultrascale
        ("default", "RAM_URAM", ),
    ),
}
