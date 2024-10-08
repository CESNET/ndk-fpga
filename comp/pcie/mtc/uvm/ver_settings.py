# ver_settings.py
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Daniel Kriz <danielkriz@cesnet.cz>

SETTINGS = {
    "default" : {
        "MFB_REGIONS"       : "2"                ,
        "MFB_REGION_SIZE"   : "1"                ,
        "MFB_BLOCK_SIZE"    : "8"                ,
        "MFB_ITEM_WIDTH"    : "32"               ,
        "BAR0_BASE_ADDR"    : "32'h01000000"     ,
        "BAR1_BASE_ADDR"    : "32'h02000000"     ,
        "BAR2_BASE_ADDR"    : "32'h03000000"     ,
        "BAR3_BASE_ADDR"    : "32'h04000000"     ,
        "BAR4_BASE_ADDR"    : "32'h05000000"     ,
        "BAR5_BASE_ADDR"    : "32'h06000000"     ,
        "EXP_ROM_BASE_ADDR" : "32'h0A000000"     ,
        "CC_PIPE"           : "1"                ,
        "CQ_PIPE"           : "1"                ,
        "MI_PIPE"           : "1"                ,
        "MI_DATA_WIDTH"     : "32"               ,
        "MI_ADDR_WIDTH"     : "32"               ,
        "DEVICE"            : "\\\"STRATIX10\\\"",
        "ENDPOINT_TYPE"     : "\\\"P_TILE\\\""   ,
        "CLK_PERIOD"        : "10ns"             ,
        "PCIE_LEN_MIN"      : "1"                ,
        "PCIE_LEN_MAX"      : "256"              ,
        "__core_params__": {"UVM_TEST": "test::base"},
    },

    "device_agilex"     : {
        "DEVICE"            : "\\\"AGILEX\\\""   ,
    },
    "device_ultrascale" : {
        "DEVICE"            : "\\\"ULTRASCALE\\\"",
        "ENDPOINT_TYPE"     : "\\\"USP\\\""       ,
    },
    "device_7series"    : {
        "DEVICE"            : "\\\"7SERIES\\\"",
        "ENDPOINT_TYPE"     : "\\\"USP\\\""    ,
    },
    "endpoint_rtile"    : {
        "ENDPOINT_TYPE"     : "\\\"R_TILE\\\"",
    },
    "endpoint_htile"    : {
        "ENDPOINT_TYPE"     : "\\\"H_TILE\\\"",
    },
    "max_payload_size_4096"     : {
        "PCIE_LEN_MAX"            : "1024"   ,
    },
    "max_payload_size_2048"     : {
        "PCIE_LEN_MAX"            : "512"   ,
    },
    "max_payload_size_512"     : {
        "PCIE_LEN_MAX"            : "128"   ,
    },
    "max_payload_size_256"     : {
        "PCIE_LEN_MAX"            : "64"   ,
    },
    "max_payload_size_128"     : {
        "PCIE_LEN_MAX"            : "32"   ,
    },
    "1_region"                 : {
        "MFB_REGIONS"             : "1"   ,
    },
    "4_region"                 : {
        "MFB_REGIONS"             : "4"   ,
    },
    "test_speed" : {
        "__core_params__": {"UVM_TEST": "test::speed"},
    },
    "_combinations_"    : (
        (                                                                         ),
        ("default"      , "endpoint_rtile",                                       ),
        ("default"      , "endpoint_htile",                                       ),
        ("device_agilex", "endpoint_rtile",                                       ),
        ("device_agilex", "endpoint_htile",                                       ),
        ("default"      , "device_ultrascale",                                    ),
        ("default"      , "device_7series",                                       ),
        ("default"      , "endpoint_rtile",    "test_speed",                      ),
        ("default"      , "endpoint_htile",    "test_speed",                      ),
        ("device_agilex", "endpoint_rtile",    "test_speed",                      ),
        ("device_agilex", "endpoint_htile",    "test_speed",                      ),
        ("default"      , "device_ultrascale", "test_speed",                      ),
        ("default"      , "device_7series",    "test_speed",                      ),
        (                                      "max_payload_size_128",            ),
        (                                      "max_payload_size_256",            ),
        (                                      "max_payload_size_512",            ),
        (                                      "max_payload_size_2048",           ),
        (                                      "max_payload_size_4096",           ),
        # ("default"      , "device_ultrascale", "max_payload_size_128",            ),
        # ("default"      , "device_ultrascale", "max_payload_size_256",            ),
        # ("default"      , "device_ultrascale", "max_payload_size_512",            ),
        # ("default"      , "device_ultrascale", "max_payload_size_2048",           ),
        # ("default"      , "device_ultrascale", "max_payload_size_4096",           ),
        (                                                              "1_region",),
        ("default"      , "device_ultrascale",                         "1_region",),
        (                                                              "4_region",),
        (                 "endpoint_rtile",                            "4_region",),
        ("default"      , "device_ultrascale",                         "4_region",),
    )
}

