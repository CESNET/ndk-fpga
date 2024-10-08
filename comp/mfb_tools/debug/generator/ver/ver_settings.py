# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "DEVICE"                 : "\\\"ULTRASCALE\\\"",
        "MFB_REGIONS"            : "4",
        "MFB_REGION_SIZE"        : "8",
        "MFB_BLOCK_SIZE"         : "8",
        "MFB_ITEM_WIDTH"         : "8",

        "LENGTH_WIDTH"           : "16",
        "CHANNELS_WIDTH"         : "4",
        "PKT_CNT_WIDTH"          : "64",
        "USE_PACP_ARCH"          : "0",
    },
    "use_pacp_arch" : {
        "USE_PACP_ARCH"          : "1",
    },
    "pcie" : {
        "MFB_REGIONS"            : "2",
        "MFB_REGION_SIZE"        : "1",
        "MFB_BLOCK_SIZE"         : "8",
        "MFB_ITEM_WIDTH"         : "32",
    },
    "region_comb_1" : {
        "MFB_REGIONS"            : "1",
        "MFB_REGION_SIZE"        : "8",
        "MFB_BLOCK_SIZE"         : "8",
        "MFB_ITEM_WIDTH"         : "8",
    },
    "region_comb_2" : {
        "MFB_REGIONS"            : "2",
        "MFB_REGION_SIZE"        : "8",
        "MFB_BLOCK_SIZE"         : "8",
        "MFB_ITEM_WIDTH"         : "8",
    },
    "region_comb_3" : {
        "MFB_REGIONS"            : "1",
        "MFB_REGION_SIZE"        : "4",
        "MFB_BLOCK_SIZE"         : "8",
        "MFB_ITEM_WIDTH"         : "8",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    (                 "use_pacp_arch",),
    # ("region_comb_1",),
    ("region_comb_1", "use_pacp_arch",),
    # ("region_comb_2",),
    ("region_comb_2", "use_pacp_arch",),
    ("region_comb_3",),
    ("region_comb_3", "use_pacp_arch",),
    ("pcie",          "use_pacp_arch",),
    ),
}
