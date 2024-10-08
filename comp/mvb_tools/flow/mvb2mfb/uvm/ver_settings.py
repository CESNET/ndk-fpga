# ver_settings.py
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "MVB_ITEMS"          : "4",
        "MVB_ITEM_WIDTH_RAW" : "536",
        "MFB_REGIONS"        : "4",
        "MFB_REGION_SIZE"    : "8",
        "MFB_BLOCK_SIZE"     : "8",
        "MFB_ITEM_WIDTH"     : "8",
        "MFB_META_WIDTH"     : "12",
        "MFB_ALIGNMENT"      : "MFB_REGION_SIZE*MFB_BLOCK_SIZE",
    },
    "region_comb_1" : {
        "MVB_ITEMS"          : "1",
        "MFB_REGIONS"        : "1",
    },
    "region_comb_2" : {
        "MVB_ITEMS"          : "2",
        "MFB_REGIONS"        : "2",
    },
    "align_low" : {
        "MFB_ALIGNMENT"      : "MFB_BLOCK_SIZE",
    },
    "mvb_item_small" : {
        "MVB_ITEM_WIDTH_RAW" : "48",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("region_comb_1",),
    ("region_comb_2",),
    ("align_low",),
    ("mvb_item_small",),
    ("region_comb_1", "align_low",),
    ("region_comb_1", "mvb_item_small",),
    ),
}
