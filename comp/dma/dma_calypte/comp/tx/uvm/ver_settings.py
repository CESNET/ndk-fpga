# ver_settings.py
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "DEVICE"                  : "\\\"ULTRASCALE\\\"",

        "MI_WIDTH"                : "32",

        "USR_MFB_REGIONS"         : "1",
        "USR_MFB_REGION_SIZE"     : "4",
        "USR_MFB_BLOCK_SIZE"      : "8",
        "USR_MFB_ITEM_WIDTH"      : "8",

        "PCIE_CQ_MFB_REGIONS"     : "1",
        "PCIE_CQ_MFB_REGION_SIZE" : "1",
        "PCIE_CQ_MFB_BLOCK_SIZE"  : "8",
        "PCIE_CQ_MFB_ITEM_WIDTH"  : "32",

        "PCIE_CC_MFB_REGIONS"     : "1",
        "PCIE_CC_MFB_REGION_SIZE" : "1",
        "PCIE_CC_MFB_BLOCK_SIZE"  : "8",
        "PCIE_CC_MFB_ITEM_WIDTH"  : "32",

        "CHANNELS"                : "2",
        "CNTRS_WIDTH"             : "64",
        "HDR_META_WIDTH"          : "24",
        "PKT_SIZE_MAX"            : "2**12",

        "DATA_POINTER_WIDTH"      : "13",
        "DMA_HDR_POINTER_WIDTH"   : "10",

        "PCIE_LEN_MAX"            : "256",
    },
    "intel_dev" : {
        "DEVICE"                  : "\\\"AGILEX\\\""
    },
    "8_channels" : {
        "CHANNELS"                : "8",
    },
    "16_channels" : {
        "CHANNELS"                : "16",
    },
    "buff_size_small" : {
        "PKT_SIZE_MAX"            : "2**9",
        "DATA_POINTER_WIDTH"      : "10",
    },
    "2_regions" : {
        "USR_MFB_REGION_SIZE" : "8",
        "PCIE_CQ_MFB_REGIONS" : "2",
        "PCIE_CC_MFB_REGIONS" : "2",
    },
    "_combinations_" : (
    (                                                            ), # default
    (             "8_channels" ,                                 ),
    # (             "8_channels" , "buff_size_small",              ),
    (                                               "2_regions", ),
    (             "16_channels",                    "2_regions", ),
    # (             "16_channels", "buff_size_small", "2_regions", ),

    ("intel_dev",                                   "2_regions", ),
    ("intel_dev", "16_channels",                    "2_regions", ),
    # ("intel_dev", "16_channels", "buff_size_small", "2_regions", ),
    ),
}
