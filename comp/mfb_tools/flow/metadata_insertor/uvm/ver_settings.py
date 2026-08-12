# ver_settings.py
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Daniel Kříž <danielkriz@cesnet.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "MVB_ITEMS"          : "2",
        "MVB_ITEM_WIDTH"     : "128",
        "MFB_REGIONS"        : "2",
        "MFB_REGION_SIZE"    : "1",
        "MFB_BLOCK_SIZE"     : "8",
        "MFB_ITEM_WIDTH"     : "32",
        "MFB_META_WIDTH"     : "2",
        "MFB_META_ALIGNMENT" : "1",
        "INSERT_MODE"        : "1",
        "MVB_FIFO_SIZE"      : "32",
        "MVB_FIFOX_MULTI"    : "1",
        "FRAME_SIZE_MAX"     : "1500",
        "FRAME_SIZE_MIN"     : "60",
    },
    "region_comb_1" : {
        "MVB_ITEMS"          : "1",
        "MFB_REGIONS"        : "8",
        "MFB_REGION_SIZE"    : "8",
        "MFB_BLOCK_SIZE"     : "8",
    },
    "region_comb_2" : {
        "MVB_ITEMS"          : "4",
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
        "MFB_REGION_SIZE"    : "64",
        "MFB_BLOCK_SIZE"     : "8",
    },
    "ins_mode_dis" : {
        "INSERT_MODE"        : "0",
        "MFB_META_ALIGNMENT" : "0",
    },
    "ins_mode_2" : {
        "INSERT_MODE"        : "2",
        "MFB_META_ALIGNMENT" : "0",
    },
    "big_frames" : {
        "FRAME_SIZE_MIN"     : "4096",
        "FRAME_SIZE_MAX"     : "8192",
        "MFB_ITEM_WIDTH"     : "32",
        "MFB_META_WIDTH"     : "32",
        "MVB_ITEM_WIDTH"     : "128",
    },
    "small_frames" : {
        "FRAME_SIZE_MIN"     : "32",
        "FRAME_SIZE_MAX"     : "512",
        "MFB_ITEM_WIDTH"     : "8",
        "MFB_META_WIDTH"     : "8",
        "MVB_ITEM_WIDTH"     : "8",
    },
    "fifo_size_0" : {
        "MVB_FIFO_SIZE"      : "0",
        "MVB_FIFOX_MULTI"    : "0",
    },
    "fifo_size_1" : {
        "MVB_FIFO_SIZE"      : "1",
        "MVB_FIFOX_MULTI"    : "0",
    },
    "shakedown" : {
        "MVB_FIFOX_MULTI"    : "0",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("region_comb_1",),
    ("region_comb_2",),
    ("region_comb_4",),
    ("region_comb_5",),
    ("shakedown",),
    ("ins_mode_dis",),
    ("ins_mode_2",),
    ("big_frames",),
    ("small_frames",),
    ("fifo_size_0",),
    ("fifo_size_1",),
    ("fifo_size_0", "region_comb_2", "big_frames",),
    ("fifo_size_1", "region_comb_2", "big_frames",),
    ),
}
