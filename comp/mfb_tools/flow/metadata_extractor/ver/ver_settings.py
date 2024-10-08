# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "MVB_ITEMS"          : "8",
        "MFB_REGIONS"        : "2",
        "MFB_REGION_SIZE"    : "1",
        "MFB_BLOCK_SIZE"     : "8",
        "MFB_ITEM_WIDTH"     : "32",
        "MFB_META_WIDTH"     : "2",
        "MFB_META_ALIGNMENT" : "1",
        "EXTRACT_MODE"       : "1",
        "OUT_MVB_PIPE_EN"    : "0",
        "OUT_MFB_PIPE_EN"    : "0",
        "FRAME_SIZE_MAX"     : "512",
        "FRAME_SIZE_MIN"     : "60",
        "TRANSACTION_COUNT"  : "2000",
    },
    "pcie" : {
        "MFB_REGIONS"        : "2",
        "MFB_REGION_SIZE"    : "1",
        "MFB_BLOCK_SIZE"     : "8",
        "MFB_ITEM_WIDTH"     : "32",
    },
    "region_comb_1" : {
        "MVB_ITEMS"          : "1",
        "MFB_REGIONS"        : "8",
        "MFB_REGION_SIZE"    : "8",
        "MFB_BLOCK_SIZE"     : "8",
    },
    "region_comb_2" : {
        "MVB_ITEMS"          : "2",
        "MFB_REGIONS"        : "8",
        "MFB_REGION_SIZE"    : "8",
        "MFB_BLOCK_SIZE"     : "8",
    },
    "region_comb_3" : {
        "MVB_ITEMS"          : "3",
        "MFB_REGIONS"        : "8",
        "MFB_REGION_SIZE"    : "8",
        "MFB_BLOCK_SIZE"     : "8",
    },
    "region_comb_4" : {
        "MVB_ITEMS"          : "1",
        "MFB_REGIONS"        : "1",
        "MFB_REGION_SIZE"    : "8",
        "MFB_BLOCK_SIZE"     : "32",
    },
    "region_comb_5" : {
        "MVB_ITEMS"          : "1",
        "MFB_REGIONS"        : "1",
        "MFB_REGION_SIZE"    : "8",
        "MFB_BLOCK_SIZE"     : "2",
    },
    "ext_mode_dis" : {
        "EXTRACT_MODE"       : "0",
        "MFB_META_ALIGNMENT" : "0",
    },
    "big_frames" : {
        "FRAME_SIZE_MIN"     : "4096",
        "FRAME_SIZE_MAX"     : "8192",
    },
    "medium_frames" : {
        "FRAME_SIZE_MIN"     : "2048",
        "FRAME_SIZE_MAX"     : "4096",
    },
    "small_frames" : {
        "FRAME_SIZE_MIN"     : "32",
        "FRAME_SIZE_MAX"     : "512",
    },
    "mvb_and_mfb_pipe_en" : {
        "OUT_MVB_PIPE_EN"    : "1",
        "OUT_MFB_PIPE_EN"    : "1",
    },
    "mvb_pipe_en" : {
        "OUT_MVB_PIPE_EN"    : "1",
        "OUT_MFB_PIPE_EN"    : "0",
    },
    "mfb_pipe_en" : {
        "OUT_MVB_PIPE_EN"    : "0",
        "OUT_MFB_PIPE_EN"    : "1",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("region_comb_1",),
    ("region_comb_2",),
    ("region_comb_3",),
    ("region_comb_4",),
    ("region_comb_5",),
    ("pcie",),
    ("ext_mode_dis",),
    ("big_frames",),
    ("medium_frames",),
    ("small_frames",),
    ("mvb_and_mfb_pipe_en",),
    ("mvb_pipe_en",),
    ("mfb_pipe_en",),
    ),
}
