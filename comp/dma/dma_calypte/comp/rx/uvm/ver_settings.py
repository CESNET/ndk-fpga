# ver_settings.py
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

# Every key must match a parameter name in tbench/tests/pkg.sv. A key that
# matches no parameter is ignored without any message and the combination then
# runs with the default value of that parameter.
SETTINGS = {
    "default" : { # The default setting of verification
        "DEVICE"              : "\\\"ULTRASCALE\\\"",

        "MI_WIDTH"            : "32",

        "USR_MFB_REGIONS"     : "1",
        "USR_MFB_REGION_SIZE" : "4",
        "USR_MFB_BLOCK_SIZE"  : "8",
        "USR_MFB_ITEM_WIDTH"  : "8",

        "PCIE_RQ_REGIONS"     : "1",
        "PCIE_RQ_REGION_SIZE" : "1",
        "PCIE_RQ_BLOCK_SIZE"  : "8",
        "PCIE_RQ_ITEM_WIDTH"  : "32",

        "CHANNELS"            : "2",
        "POINTER_WIDTH"       : "16",
        "SW_ADDR_WIDTH"       : "64",
        "CNTRS_WIDTH"         : "64",
        "PKT_SIZE_MAX"        : "2**12",
        "TRBUF_REG_EN"        : "0",
    },
    "2_regions"  : {
        "USR_MFB_REGION_SIZE" : "8",
        "PCIE_RQ_REGIONS"     : "2",
    },
    "16_channels" : {
        "CHANNELS"            : "16",
    },
    "32_channels" : {
        "CHANNELS"            : "32",
    },
    "trbuf_reg_en" : {
        "TRBUF_REG_EN"        : "1",
    },
    "intel_dev" : {
        "DEVICE"              : "\\\"AGILEX\\\"",
    },
    "_combinations_" : (
    (                                           ), # default
    ("32_channels",              "trbuf_reg_en",),
    ("16_channels", "2_regions", "trbuf_reg_en",),
    ("16_channels",              "trbuf_reg_en", "intel_dev",),
    ("16_channels", "2_regions", "trbuf_reg_en", "intel_dev",),
    ),
}
