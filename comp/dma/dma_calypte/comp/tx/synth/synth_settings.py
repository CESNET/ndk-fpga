# synth_settings.py
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Vladislav Valek <valekv@cesnet.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "DEVICE"                    : "\\\"ULTRASCALE\\\"",
        "MI_WIDTH"                  : "32",

        "USR_TX_MFB_REGIONS"        : "1",
        "USR_TX_MFB_REGION_SIZE"    : "4",
        "USR_TX_MFB_BLOCK_SIZE"     : "8",
        "USR_TX_MFB_ITEM_WIDTH"     : "8",

        "PCIE_CQ_MFB_REGIONS"       : "1",
        "PCIE_CQ_MFB_REGION_SIZE"   : "1",
        "PCIE_CQ_MFB_BLOCK_SIZE"    : "8",
        "PCIE_CQ_MFB_ITEM_WIDTH"    : "32",

        "PCIE_CC_MFB_REGIONS"       : "1",
        "PCIE_CC_MFB_REGION_SIZE"   : "1",
        "PCIE_CC_MFB_BLOCK_SIZE"    : "8",
        "PCIE_CC_MFB_ITEM_WIDTH"    : "32",

        "DATA_POINTER_WIDTH"        : "13",
        "DMA_HDR_POINTER_WIDTH"     : "13",

        "CHANNELS"                  : "8",
        "CNTRS_WIDTH"               : "64",
        "HDR_META_WIDTH"            : "24",
        "PKT_SIZE_MAX"              : "2**12",
    },
    "2_regions": {
        "USR_TX_MFB_REGION_SIZE"    : "8",
        "PCIE_CQ_MFB_REGIONS"       : "2",
        "PCIE_CC_MFB_REGIONS"       : "2",
    },
    "minimal_buffer" : {
        "DATA_POINTER_WIDTH" : "10",
        "PKT_SIZE_MAX" : "2**9",
    },
    "4_channels" : {
        "CHANNELS" : "4",
    },
    "32_channels" : {
        "CHANNELS" : "32",
    },
    "_combinations_" : (
        (), # Works the same as '("default",),' as the "default" is applied in every combination
        (                            "minimal_buffer",),

        (             "4_channels",                   ),
        (             "4_channels",  "minimal_buffer",),

        (             "32_channels",                  ),
        (             "32_channels", "minimal_buffer",),
        ("2_regions",                                 ),
        ("2_regions",                "minimal_buffer",),

        ("2_regions", "4_channels",                   ),
        ("2_regions", "4_channels",  "minimal_buffer",),

        ("2_regions", "32_channels",                  ),
        ("2_regions", "32_channels", "minimal_buffer",),
    ),
}
