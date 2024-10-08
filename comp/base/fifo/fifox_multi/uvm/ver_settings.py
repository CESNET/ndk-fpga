# ver_settings.py
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    "default" : { # The default setting of verification
        "DATA_WIDTH"            : "512",
        "ITEMS"                 : "512",
        "WRITE_PORTS"           : "4",
        "READ_PORTS"            : "2",
        "RAM_TYPE"              : "\\\"AUTO\\\"",
        "DEVICE"                : "\\\"ULTRASCALE\\\"",
        "ALMOST_FULL_OFFSET"    : "0",
        "ALMOST_EMPTY_OFFSET"   : "0",
        "ALLOW_SINGLE_FIFO"     : "0",
        "SAFE_READ_MODE"        : "0",
        "IMPL_SHAKEDOWN"        : "0",
        "MIN_TRANSACTION_COUNT" : "4000",
        "MAX_TRANSACTION_COUNT" : "5000",
    },

    "IMPL_SHAKEDOWN_ON" : {
        "IMPL_SHAKEDOWN" : "1",
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
    },"ALMOST_FULL_OFFSET_71" : {
        "ALMOST_FULL_OFFSET" : "71",
    },

    "ALMOST_EMPTY_OFFSET_3" : {
        "ALMOST_EMPTY_OFFSET" : "3",
    },
    "ALMOST_EMPTY_OFFSET_54" : {
        "ALMOST_EMPTY_OFFSET" : "54",
    },

    "SIZE_SMALL" : {
        "WRITE_PORTS" : "1",
        "READ_PORTS"  : "1",
        "DATA_WIDTH"  : "1",
        "ITEMS"       : "2",
    },
    "SIZE_BIG" : {
        "WRITE_PORTS" : "30",
        "READ_PORTS"  : "23",
        "DATA_WIDTH"  : "4000",
        "ITEMS"       : "2048",
    },

    "SAFE_READ_MODE_ON" : {
        "SAFE_READ_MODE" : "1",
    },

    "_combinations_" : (
        # '()' works the same as '("default",)'. "default" is applied in every combination

        (),
        ("IMPL_SHAKEDOWN_ON",),

        ("SIZE_SMALL", "DEVICE_7SERIES", "SAFE_READ_MODE_ON",),
        ("SIZE_BIG",   "DEVICE_ARRIA10",   "ALMOST_FULL_OFFSET_71", "ALMOST_EMPTY_OFFSET_54",),
        (              "DEVICE_STRATIX10", "ALMOST_FULL_OFFSET_5",  "ALMOST_EMPTY_OFFSET_3", ),

        ("IMPL_SHAKEDOWN_ON", "SIZE_SMALL", "DEVICE_7SERIES", "SAFE_READ_MODE_ON",),
        ("IMPL_SHAKEDOWN_ON", "SIZE_BIG",   "DEVICE_ARRIA10",   "ALMOST_FULL_OFFSET_71", "ALMOST_EMPTY_OFFSET_54",),
        ("IMPL_SHAKEDOWN_ON",               "DEVICE_STRATIX10", "ALMOST_FULL_OFFSET_5",  "ALMOST_EMPTY_OFFSET_3", ),

        (                     "DEVICE_AGILEX", "ALMOST_FULL_OFFSET_5", "ALMOST_EMPTY_OFFSET_3", "SAFE_READ_MODE_ON",),
        ("IMPL_SHAKEDOWN_ON", "DEVICE_AGILEX", "ALMOST_FULL_OFFSET_5", "ALMOST_EMPTY_OFFSET_3", "SAFE_READ_MODE_ON",),

        (                    "SIZE_BIG", "ALMOST_FULL_OFFSET_5", "ALMOST_EMPTY_OFFSET_54", "SAFE_READ_MODE_ON",),
        ("IMPL_SHAKEDOWN_ON","SIZE_BIG", "ALMOST_FULL_OFFSET_5", "ALMOST_EMPTY_OFFSET_54", "SAFE_READ_MODE_ON",),

    ),
}
