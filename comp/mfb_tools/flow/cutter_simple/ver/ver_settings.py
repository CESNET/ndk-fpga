# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "REGIONS"            : "2",
        "REGION_SIZE"        : "8",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
        "CUTTED_ITEMS"       : "27",
        "MAX_CUT_OFFSET"     : "64",
        "FRAME_SIZE_MAX"     : "512",
        "FRAME_SIZE_MIN"     : "64+CUTTED_ITEMS+MAX_CUT_OFFSET",
        "TRANSACTION_COUNT"  : "2000",
    },
    "pcie" : {
        "REGIONS"            : "2",
        "REGION_SIZE"        : "1",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "32",
    },
    "region_comb_1" : {
        "REGIONS"            : "1",
        "REGION_SIZE"        : "8",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
    },
    "region_comb_2" : {
        "REGIONS"            : "4",
        "REGION_SIZE"        : "8",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
    },
    "region_comb_3" : {
        "REGIONS"            : "1",
        "REGION_SIZE"        : "1",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
    },
    "region_comb_4" : {
        "REGIONS"            : "1",
        "REGION_SIZE"        : "2",
        "BLOCK_SIZE"         : "4",
        "ITEM_WIDTH"         : "8",
    },
    "region_comb_5" : {
        "REGIONS"            : "1",
        "REGION_SIZE"        : "2",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
    },
    "region_comb_6" : {
        "REGIONS"            : "1",
        "REGION_SIZE"        : "4",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
    },
    "cutted_items_max" : {
        "CUTTED_ITEMS"       : "REGION_SIZE*BLOCK_SIZE",
        "FRAME_SIZE_MIN"     : "64+(REGION_SIZE*BLOCK_SIZE)+MAX_CUT_OFFSET"
    },
    "cutted_items_comb_1" : {
        "CUTTED_ITEMS"          : "1",
    },
    "cut_offset_0" : {
        "MAX_CUT_OFFSET" : "0"
    },
    "cut_offset_1" : {
        "MAX_CUT_OFFSET" : "1"
    },
    "cut_offset_small" : {
        "MAX_CUT_OFFSET" : "2"
    },
    "cut_offset_large" : {
        "MAX_CUT_OFFSET" : "128"
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("region_comb_1",),
    ("region_comb_2",),
    ("region_comb_6",),

    ("cutted_items_max",),

    ("cut_offset_0",),
    ("cut_offset_1",),
    ("cut_offset_small",),
    ("cut_offset_large",),

    ("pcie", "cutted_items_max",),
    ("pcie", "cutted_items_max", "cut_offset_small",),
    ("pcie", "cutted_items_max", "cut_offset_large",),
    ("pcie", "cutted_items_comb_1",),
    ("pcie", "cutted_items_comb_1", "cut_offset_small",),
    ("pcie", "cutted_items_comb_1", "cut_offset_large",),

    ("region_comb_1", "cutted_items_max",),
    ("region_comb_1", "cutted_items_max", "cut_offset_small",),
    ("region_comb_1", "cutted_items_max", "cut_offset_large",),
    ("region_comb_1", "cutted_items_comb_1",),
    ("region_comb_1", "cutted_items_comb_1", "cut_offset_small",),
    ("region_comb_1", "cutted_items_comb_1", "cut_offset_large",),

    ("region_comb_2", "cutted_items_comb_1",),
    ("region_comb_2", "cutted_items_comb_1", "cut_offset_small",),
    ("region_comb_2", "cutted_items_comb_1", "cut_offset_large",),

    ("region_comb_3", "cutted_items_max",),
    ("region_comb_3", "cutted_items_comb_1",),

    ("region_comb_4", "cutted_items_max",),
    ("region_comb_4", "cutted_items_comb_1",),

    ("region_comb_5", "cutted_items_max",),
    ("region_comb_5", "cutted_items_comb_1",),

    ("region_comb_6", "cutted_items_max",),
    ("region_comb_6", "cutted_items_comb_1",),
    ),
}
