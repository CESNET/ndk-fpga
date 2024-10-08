# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "REGIONS"            : "2",
        "REGION_SIZE"        : "8",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
        "LEN_WIDTH"          : "8",
        "TRANSACTION_COUNT"  : "2000",
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
        "REGION_SIZE"        : "2",
        "BLOCK_SIZE"         : "4",
        "ITEM_WIDTH"         : "8",
    },
    "region_comb_4" : {
        "REGIONS"            : "1",
        "REGION_SIZE"        : "2",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
    },
    "region_comb_5" : {
        "REGIONS"            : "1",
        "REGION_SIZE"        : "4",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
    },
    "len_width_comb_1" : {
        "LEN_WIDTH"          : "14",
    },
    "len_width_comb_2" : {
        "LEN_WIDTH"          : "16",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("region_comb_1",),
    ("region_comb_3",),
    ("region_comb_4",),
    ("region_comb_5",),

    ("region_comb_1", "len_width_comb_1",),
    ("region_comb_1", "len_width_comb_2",),

    ("region_comb_2", "len_width_comb_1",),
    ("region_comb_2", "len_width_comb_2",),

    ("region_comb_3", "len_width_comb_1",),
    ("region_comb_3", "len_width_comb_2",),

    ("region_comb_4", "len_width_comb_1",),
    ("region_comb_4", "len_width_comb_2",),

    ("region_comb_5", "len_width_comb_1",),
    ("region_comb_5", "len_width_comb_2",),
    ),
}
