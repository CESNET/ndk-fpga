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
        "MVB_FIFO_SIZE"      : "0",
        "FRAME_SIZE_MAX"     : "1500",
        "FRAME_SIZE_MIN"     : "60",
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
    "region_comb_6" : {
        "MFB_REGIONS"        : "4",
    },
    "region_comb_7" : {
        "MFB_REGIONS"        : "16",
    },
    "region_comb_8" : {
        "MFB_REGIONS"        : "32",
    },
    "region_size_comb" : {
        "MFB_REGION_SIZE"    : "4",
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
    "medium_frames" : {
        "FRAME_SIZE_MIN"     : "2048",
        "FRAME_SIZE_MAX"     : "4096",
        "MFB_ITEM_WIDTH"     : "16",
        "MFB_META_WIDTH"     : "16",
        "MVB_ITEM_WIDTH"     : "32",
    },
    "small_frames" : {
        "FRAME_SIZE_MIN"     : "32",
        "FRAME_SIZE_MAX"     : "512",
        "MFB_ITEM_WIDTH"     : "8",
        "MFB_META_WIDTH"     : "8",
        "MVB_ITEM_WIDTH"     : "8",
    },
    "fifo_size_1" : {
        "MVB_FIFO_SIZE"      : "1",
    },
    "fifo_size_2" : {
        "MVB_FIFO_SIZE"      : "2",
    },
    "fifo_size_3" : {
        "MVB_FIFO_SIZE"      : "3",
    },
    "fifo_size_4" : {
        "MVB_FIFO_SIZE"      : "4",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("region_comb_1",),
    ("region_comb_2",),
    ("region_comb_3",),
    ("region_comb_4",),
    ("region_comb_5",),
    ("pcie",),
    ("ins_mode_dis",),
    ("ins_mode_2",),
    ("big_frames",),
    ("medium_frames",),
    ("small_frames",),
    ("fifo_size_1",),
    ("fifo_size_2",),
    ("fifo_size_3",),
    ("fifo_size_4",),
    ("fifo_size_2", "medium_frames", "region_comb_3"),
    ("fifo_size_2", "ins_mode_dis", "small_frames", "region_comb_2"),
    ("fifo_size_4", "medium_frames", "region_comb_3"),
    ("fifo_size_2", "ins_mode_dis", "small_frames", "region_comb_6", "region_size_comb"),
    ("fifo_size_3", "ins_mode_2", "small_frames", "region_comb_6", "region_size_comb"),
    ("fifo_size_4", "small_frames", "region_comb_6", "region_size_comb"),
    ("fifo_size_2", "ins_mode_2", "small_frames", "region_comb_7", "region_size_comb"),
    ("fifo_size_3", "ins_mode_dis", "small_frames", "region_comb_7", "region_size_comb"),
    ("fifo_size_4", "small_frames", "region_comb_7", "region_size_comb"),
    ("fifo_size_2", "ins_mode_dis", "small_frames", "region_comb_8", "region_size_comb"),
    ("fifo_size_3", "ins_mode_2", "small_frames", "region_comb_8", "region_size_comb"),
    ("fifo_size_4", "small_frames", "region_comb_8", "region_size_comb"),
    ),
}
