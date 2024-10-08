# ver_settings.py
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "MFB_REGIONS"        : "4",
        "MFB_REGION_SIZE"    : "8",
        "MFB_BLOCK_SIZE"     : "8",
        "MFB_ITEM_WIDTH"     : "8",
        "MFB_META_WIDTH"     : "16",
        "USE_PIPE"           : "0",
        "FRAME_SIZE_MIN"     : "60",
        "FRAME_SIZE_MAX"     : "1500",
    },
    "pcie" : {
        "MFB_REGIONS"        : "2",
        "MFB_REGION_SIZE"    : "1",
        "MFB_BLOCK_SIZE"     : "8",
        "MFB_ITEM_WIDTH"     : "32",
    },
    "one_region" : {
        "MFB_REGIONS"        : "1",
    },
    "pipe_enabled" : {
        "USE_PIPE"           : "1",
    },
    "big_frames" : {
        "FRAME_SIZE_MIN"     : "1500",
        "FRAME_SIZE_MAX"     : "5000",
        "MFB_META_WIDTH"     : "31",
    },
    "small_frames" : {
        "FRAME_SIZE_MIN"     : "32",
        "FRAME_SIZE_MAX"     : "100",
        "MFB_META_WIDTH"     : "5",
    },
    "_combinations_" : (
    (                                             ), # Works the same as '("default",),' as the "default" is applied in every combination
    ("pcie"      ,                                ),
    ("one_region",                                ),
    ("one_region", "pipe_enabled",                ),
    ("pcie"      , "pipe_enabled",                ),
    (              "pipe_enabled",                ),
    (                              "big_frames"  ,),
    ("pcie"      ,                 "big_frames"  ,),
    ("one_region",                 "big_frames"  ,),
    ("one_region",                 "small_frames",),
    ("pcie"      ,                 "small_frames",),
    (                              "small_frames",),
    ),
}
