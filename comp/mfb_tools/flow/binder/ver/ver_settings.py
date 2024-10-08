# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "REGIONS"            : "4",
        "REGION_SIZE"        : "8",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
        "FRAME_SIZE_MAX"     : "512",
        "FRAME_SIZE_MIN"     : "60",
        "TRANSACTION_COUNT"  : "8000",
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
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ),
}
