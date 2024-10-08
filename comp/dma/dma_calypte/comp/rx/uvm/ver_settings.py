# ver_settings.py
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "DEVICE"                  : "\\\"ULTRASCALE\\\"",

        "MI_WIDTH"                : "32",

        "USER_MFB_REGIONS"        : "1",
        "USER_MFB_REGION_SIZE"    : "4",
        "USER_MFB_BLOCK_SIZE"     : "8",
        "USER_MFB_ITEM_WIDTH"     : "8",

        "PCIE_UP_MFB_REGIONS"     : "1",
        "PCIE_UP_MFB_REGION_SIZE" : "1",
        "PCIE_UP_MFB_BLOCK_SIZE"  : "8",
        "PCIE_UP_MFB_ITEM_WIDTH"  : "32",

        "CHANNELS"                : "2",
        "POINTER_WIDTH"           : "16",
        "SW_ADDR_WIDTH"           : "64",
        "CNTRS_WIDTH"             : "64",
        "PKT_SIZE_MAX"            : "2**12",
        "OPT_BUFF"                : "0",
        "TRBUF_REG_EN"            : "0",

        "PCIE_LEN_MIN"            : "1",
        "PCIE_LEN_MAX"            : "256",
    },
    "2_regions"  : {
        "USER_MFB_REGION_SIZE"    : "8",
        "PCIE_UP_MFB_REGIONS"     : "2",
    },
    "16_channels" : {
        "CHANNELS"                : "16",
    },
    "32_channels" : {
        "CHANNELS"                : "32",
    },
    "trbuf_reg_en" : {
        "TRBUF_REG_EN"            : "1",
    },
    "intel_dev" : {
        "DEVICE"                  : "\\\"AGILEX\\\"",
    },
    "_combinations_" : (
    # (                                           ), # default
    # ("16_channels",                             ),
    ("32_channels",                             ),

    (               "2_regions",                ),
    # ("32_channels", "2_regions",                ),
    # ("16_channels", "2_regions",                ),
    #
    # (                            "trbuf_reg_en",),
    ("16_channels",              "trbuf_reg_en",),
    # ("32_channels",              "trbuf_reg_en",),
    # (               "2_regions", "trbuf_reg_en",),
    ("32_channels", "2_regions", "trbuf_reg_en",),
    # ("16_channels", "2_regions", "trbuf_reg_en",),

    # (               "2_regions",                 "intel_dev",),
    ("16_channels", "2_regions",                 "intel_dev",),
    ),
}
