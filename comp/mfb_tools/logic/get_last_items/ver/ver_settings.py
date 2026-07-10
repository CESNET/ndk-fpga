# ver_settings.py
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "REGIONS"           : "4",
        "REGION_SIZE"       : "8",
        "BLOCK_SIZE"        : "8",
        "ITEM_WIDTH"        : "8",
        "EXTRACTED_ITEMS"   : "7",
        "FRAME_SIZE_MAX"    : "4000",
        "FRAME_SIZE_MIN"    : "EXTRACTED_ITEMS",
        "TRANSACTION_COUNT" : "10000",
    },
    "region1" : {
        "REGIONS"           : "1",
    },
    "region2" : {
        "REGIONS"           : "2",
    },
    "pcie" : {
        "REGIONS"           : "2",
        "REGION_SIZE"       : "1",
        "BLOCK_SIZE"        : "8",
        "ITEM_WIDTH"        : "32",
    },
    "item32" : {
        "ITEM_WIDTH"        : "32",
    },
    "ext_item_max" : {
        "EXTRACTED_ITEMS"   : "REGION_SIZE*BLOCK_SIZE",
    },
    "ext_item_min" : {
        "EXTRACTED_ITEMS"   : "1",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("region1",),
    ("region2",),
    ("pcie",),
    ("item32",),
    ("ext_item_max",),
    ("ext_item_min",),
    ),
}
