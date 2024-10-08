# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "REGIONS"           : "2",
        "REGION_SIZE"       : "8",
        "BLOCK_SIZE"        : "8",
        "ITEM_WIDTH"        : "8",
        "EXTRACTED_ITEMS"   : "7",
        "EXTRACTED_OFFSET"  : "27",
        "FRAME_SIZE_MAX"    : "512",
        "FRAME_SIZE_MIN"    : "60",
        "TRANSACTION_COUNT" : "5000",
    },
    "pcie" : {
        "REGIONS"           : "2",
        "REGION_SIZE"       : "1",
        "BLOCK_SIZE"        : "8",
        "ITEM_WIDTH"        : "32",
    },
    "region1" : {
        "REGIONS"           : "1",
    },
    "region4" : {
        "REGIONS"           : "4",
    },
    "ext_off0" : {
        "EXTRACTED_OFFSET"  : "0",
    },
    "ext_item_max" : {
        "FRAME_SIZE_MIN"    : "REGION_SIZE*BLOCK_SIZE+EXTRACTED_OFFSET",
        "EXTRACTED_ITEMS"   : "REGION_SIZE*BLOCK_SIZE",
    },
    "ext_item_mtu" : {
        "FRAME_SIZE_MAX"    : "EXTRACTED_ITEMS",
    },
    "ext_item_min" : {
        "EXTRACTED_ITEMS"   : "1",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("region1",),
    ("region4",),
    ("ext_off0",),
    ("ext_item_min",),
    ("ext_item_max",),
    ("ext_item_mtu",),
    ("region4","ext_off0","ext_item_min",),
    ("pcie",),
    ("pcie","region1",),
    ("pcie","ext_off0","ext_item_min",),
    ),
}
