# ver_settings.py
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "RX_MFB_REGIONS"    : "4",
        "RX_MFB_REGION_S"   : "8",
        "RX_MFB_BLOCK_S"    : "8",
        "RX_MFB_ITEM_W"     : "8",
        "USERMETA_W"        : "32",
        "MOD_W"             : "5",
        "FRAME_SIZE_MAX"    : "1024",
        "FRAME_SIZE_MIN"    : "128",
    },
    "region_comb_1" : {
        "RX_MFB_REGIONS"    : "1",
        "RX_MFB_REGION_S"   : "8",
        "RX_MFB_BLOCK_S"    : "8",
        "RX_MFB_ITEM_W"     : "8",
    },
    "region_comb_2" : {
        "RX_MFB_REGIONS"    : "2",
        "RX_MFB_REGION_S"   : "8",
        "RX_MFB_BLOCK_S"    : "8",
        "RX_MFB_ITEM_W"     : "8",
    },
    "big_frames" : {
        "FRAME_SIZE_MIN"    : "4096",
        "FRAME_SIZE_MAX"    : "8192",
        "MOD_W"             : "7",
    },

    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("region_comb_1",),
    ("region_comb_2",),
    ("big_frames",),
    ),
}
