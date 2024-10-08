# synth_settings.py
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Vladislav Valek <valekv@cesnet.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "DEVICE"                  : "\\\"ULTRASCALE\\\"",

        "USR_MFB_REGIONS"         : "1",
        "USR_MFB_REGION_SIZE"     : "4",
        "USR_MFB_BLOCK_SIZE"      : "8",
        "USR_MFB_ITEM_WIDTH"      : "8",

        "PCIE_RQ_MFB_REGIONS"     : "1",
        "PCIE_RQ_MFB_REGION_SIZE" : "1",
        "PCIE_RQ_MFB_BLOCK_SIZE"  : "8",
        "PCIE_RQ_MFB_ITEM_WIDTH"  : "32",

        "PCIE_CQ_MFB_REGIONS"     : "1",
        "PCIE_CQ_MFB_REGION_SIZE" : "1",
        "PCIE_CQ_MFB_BLOCK_SIZE"  : "8",
        "PCIE_CQ_MFB_ITEM_WIDTH"  : "32",

        "HDR_META_WIDTH"          : "24",

        "RX_CHANNELS"             : "8",
        "RX_PTR_WIDTH"            : "16",
        "USR_RX_PKT_SIZE_MAX"     : "2**12",
        "TRBUF_REG_EN"            : "FALSE",

        "TX_CHANNELS"             : "8",
        "TX_PTR_WIDTH"            : "13",
        "USR_TX_PKT_SIZE_MAX"     : "2**12",

        "DSP_CNT_WIDTH"           : "64",
        "RX_GEN_EN"               : "TRUE",
        "TX_GEN_EN"               : "TRUE",
        "ST_SP_DBG_SIGNAL_W"      : "4",
        "MI_WIDTH"                : "32",
    },
    "vivado" : {
        "DEVICE" : "\\\"ULTRASCALE\\\"",
    },
    "2_regions" : {
        "USR_MFB_REGION_SIZE"   : "8",
        "PCIE_RQ_MFB_REGIONS"   : "2",
        "PCIE_CQ_MFB_REGIONS"   : "2",
    },
    "16_channel_comb" : {
        "RX_CHANNELS" : "16",
        "TX_CHANNELS" : "16",
    },
    "32_channel_comb" : {
        "RX_CHANNELS" : "32",
        "TX_CHANNELS" : "32",
    },
    "64_channel_comb" : {
        "RX_CHANNELS" : "64",
        "TX_CHANNELS" : "64",
    },
    "trbuf_reg" : {
        "TRBUF_REG_EN" : "TRUE",
    },
    "_combinations_" : (
        (), # Works the same as '("default",),' as the "default" is applied in every combination
        ("16_channel_comb",),
        ("32_channel_comb",),
        ("64_channel_comb",),

        ("16_channel_comb","trbuf_reg",),
        ("32_channel_comb","trbuf_reg",),
        ("64_channel_comb","trbuf_reg",),

        ("2_regions",),
        ("2_regions","16_channel_comb",),
        ("2_regions","32_channel_comb",),
        ("2_regions","64_channel_comb",),

        ("trbuf_reg",),
        ("2_regions","trbuf_reg",),
        ("2_regions","16_channel_comb","trbuf_reg",),
        ("2_regions","32_channel_comb","trbuf_reg",),
        ("2_regions","64_channel_comb","trbuf_reg",),
    ),
}
