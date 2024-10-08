# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "FRAME_SIZE_MAX"    : "1500",
        "FRAME_SIZE_MIN"    : "60",
        "TRANSACTION_COUNT" : "5000",
        "FLU_CLK_PERIOD"    : "5ns",
        "CMAC_CLK_PERIOD"   : "3.1ns",
        "MI_CLK_PERIOD"     : "7ns",
    },
    "frames_big" : {
        "FRAME_SIZE_MAX"    : "4096",
        "FRAME_SIZE_MIN"    : "1024",
    },
    "frames_small" : {
        "FRAME_SIZE_MAX"    : "128",
        "FRAME_SIZE_MIN"    : "50",
    },
    "flu_slow" : {
        "FLU_CLK_PERIOD"    : "9ns",
    },

    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("frames_big",),
    ("frames_small",),
    ("flu_slow","frames_small",),
    ("flu_slow",),
    ),
}
