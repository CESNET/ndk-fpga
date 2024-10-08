# ver_settings.py
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "MFB_REGIONS"     : "1",
        "MFB_REGION_SIZE" : "8",
        "MFB_BLOCK_SIZE"  : "8",
        "MFB_ITEM_WIDTH"  : "8",
        "MFB_META_WIDTH"  : "0",
        "PKT_MTU"         : "512",
        "OFFSET_WIDTH"    : "9",
        "LENGTH_WIDTH"    : "9",
        "__core_params__": {"UVM_TEST": "test::ex_test"},
    },
    "4_regions" : {
        "MFB_REGIONS"     : "4",
    },
    "region_size_1" : {
        "MFB_REGION_SIZE" : "1",
    },
    "block_size_1" : {
        "MFB_BLOCK_SIZE" : "1",
    },
    "item_width_32" : {
        "MFB_ITEM_WIDTH" : "32",
    },
    "small_mtu" : {
        "PKT_MTU"         : "100",
        "OFFSET_WIDTH"    : "7",
        "LENGTH_WIDTH"    : "7",
    },
    "large_mtu" : { # long runtime (!)
        "PKT_MTU"         : "10000", # max for simulation, official max is 16383
        "OFFSET_WIDTH"    : "13",
        "LENGTH_WIDTH"    : "13",
    },
    "small_offsets" : {
        "OFFSET_WIDTH"    : "2",
    },
    "small_lengths" : {
        "LENGTH_WIDTH"    : "2",
    },
    "test_speed" : {
        "__core_params__": {"UVM_TEST": "test::speed"},
    },
    "_combinations_" : (
    (                                                                                                            ), # default
    (             "small_mtu",                                                                                   ),
    (                           "test_speed", ), # default
    (             "small_mtu",  "test_speed", ),
    (             "small_mtu", "small_offsets",                                                                  ),
    (             "small_mtu",                  "small_lengths",                                                 ),
    (             "small_mtu", "small_offsets", "small_lengths",                                                 ),
    (                                                            "region_size_1",                                ),
    (                                                                             "block_size_1",                ),
    # (                                                            "region_size_1", "block_size_1",                ), # not supported yet
    (             "small_mtu",                                   "region_size_1",                "item_width_32",),
    # ("4_regions", "small_mtu",                                   "region_size_1",                "item_width_32",), # not supported yet
    # ("4_regions",                                                "region_size_1", "block_size_1",                ), # not supported yet
    ("4_regions",                                                                 "block_size_1",                ),
    # ("4_regions",                                                "region_size_1",                                ), # not supported yet
    ("4_regions", "small_mtu", "small_offsets", "small_lengths",                                                 ),
    ("4_regions", "small_mtu",                  "small_lengths",                                                 ),
    ("4_regions", "small_mtu", "small_offsets",                                                                  ),
    ("4_regions", "small_mtu",                                                                                   ),
    ("4_regions",                                                                                                ),
    # (             "large_mtu",                                                                                   ), # long runtime
    # ("4_regions", "large_mtu",                                                                                   ), # long runtime
    ),
}
