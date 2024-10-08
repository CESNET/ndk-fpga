# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "REGIONS"            : "4",
        "REGION_SIZE"        : "8",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
        "LNG_WIDTH"          : "14",
        "SATURATION"         : "0",
        "FRAME_SIZE_MAX"     : "512",
        "FRAME_SIZE_MIN"     : "60",
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
        "REGIONS"            : "2",
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
        "REGIONS"            : "16",
        "REGION_SIZE"        : "1",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
    },
    "region_comb_6" : {
        "REGIONS"            : "1",
        "REGION_SIZE"        : "4",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
    },
    "lng_width_comb_2" : {
        "LNG_WIDTH"          : "28",
    },
    "lng_width_comb_3" : {
        "LNG_WIDTH"          : "9",
    },
    "saturation" : {
        "LNG_WIDTH"          : "9",
        "SATURATION"         : "1",
        "FRAME_SIZE_MAX"     : "1024",
        "FRAME_SIZE_MIN"     : "60",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("region_comb_1",),
    ("region_comb_2",),
    ("region_comb_3",),
    ("region_comb_4",),
    ("region_comb_5",),
    ("region_comb_6",),
    ("pcie",),

    ("lng_width_comb_2",),

    ("pcie", "lng_width_comb_2",),
    ("pcie", "lng_width_comb_3",),
    ("pcie", "saturation",),

    ("region_comb_1", "lng_width_comb_2",),
    ("region_comb_1", "lng_width_comb_3",),

    ("region_comb_2", "lng_width_comb_3",),

    ("region_comb_3", "lng_width_comb_2",),
    ("region_comb_3", "lng_width_comb_3",),

    ("region_comb_4", "lng_width_comb_2",),
    ("region_comb_4", "lng_width_comb_3",),

    ("region_comb_5", "lng_width_comb_2",),
    ("region_comb_5", "saturation",),

    ("region_comb_6", "lng_width_comb_2",),
    ("region_comb_6", "lng_width_comb_3",),
    ),
}
