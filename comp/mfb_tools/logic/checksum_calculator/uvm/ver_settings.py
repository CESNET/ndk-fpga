# ver_settings.py
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "MFB_REGIONS"     : "1",
        "MFB_REGION_SIZE" : "8",
        "MFB_BLOCK_SIZE"  : "8",
        "MFB_ITEM_SIZE"   : "8",
        "OFFSET_WIDTH"    : "7",
        "LENGTH_WIDTH"    : "9",
        "MVB_DATA_WIDTH"  : "16",
        "PKT_MTU"         : "2**12",
        "DEVICE"          : "\\\"STRATIX10\\\"",
    },
    "2_regions" : {
        "MFB_REGIONS"     : "2",
    },
    "4_regions" : {
        "MFB_REGIONS"     : "4",
    },
    "region_size_2" : {
        "MFB_REGION_SIZE" : "2",
    },
    "region_size_4" : {
        "MFB_REGION_SIZE" : "4",
    },
    "_combinations_" : (
    (                                             ), # default
    (             "region_size_2",                ),
    # (             "region_size_4",                ),
    # ("2_regions",                                 ),
    # ("2_regions", "region_size_2",                ),
    # ("2_regions", "region_size_4",                ),
    # ("4_regions", "region_size_2",                ),
    ("4_regions", "region_size_4",                ),
    ("4_regions",                                 ),
    ),

}
