# ver_settings.py
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "MFB_REGIONS"       : "1",
        "MFB_REGION_SIZE"   : "8",
        "MFB_BLOCK_SIZE"    : "8",
        "MFB_ITEM_SIZE"     : "8",
        "MFB_META_WIDTH"    : "10",
        "CLK_FREQUENCY"     : "200000000",
        "TIMESTAMP_WIDTH"   : "48",
        "TIMESTAMP_FORMAT"  : "0",
        "AUTORESET_TIMEOUT" : "1000000",
        "BUFFER_SIZE"       : "2048",
        "QUEUES"            : "1",
        "PKT_MTU"           : "2**12",
        "DEVICE"            : "\\\"STRATIX10\\\"",
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
    (             "region_size_4",                ),
    # ("2_regions",                                 ),
    # ("2_regions", "region_size_2",                ),
    # ("2_regions", "region_size_4",                ),
    # ("4_regions", "region_size_2",                ),
    # ("4_regions", "region_size_4",                ),
    # ("4_regions",                                 ),
    ),

}
