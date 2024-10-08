# synth_settings.py
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Vladislav Valek <valekv@cesnet.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "DEVICE"                    : "\\\"ULTRASCALE\\\"",
        "MI_WIDTH"                  : "32",
        "USER_RX_MFB_REGIONS"       : "1",
        "USER_RX_MFB_REGION_SIZE"   : "4",
        "USER_RX_MFB_BLOCK_SIZE"    : "8",
        "USER_RX_MFB_ITEM_WIDTH"    : "8",
        "PCIE_UP_MFB_REGIONS"       : "1",
        "PCIE_UP_MFB_REGION_SIZE"   : "1",
        "PCIE_UP_MFB_BLOCK_SIZE"    : "8",
        "PCIE_UP_MFB_ITEM_WIDTH"    : "32",
        "CHANNELS"                  : "8",
        "POINTER_WIDTH"             : "16",
        "SW_ADDR_WIDTH"             : "64",
        "CNTRS_WIDTH"               : "64",
        "HDR_META_WIDTH"            : "24",
        "PKT_SIZE_MAX"              : "2**12",
        "OPTIONAL_TRBUF_FIFO"       : "FALSE",
    },
    "vivado" : {
        "DEVICE" : "\\\"ULTRASCALE\\\"",
    },
    "512bit_variant" : {
        "USER_RX_MFB_REGION_SIZE"   : "8",
        "PCIE_UP_MFB_REGIONS"       : "2",
    },
    "16_channel_comb" : {
        "CHANNELS" : "16",
    },
    "32_channel_comb" : {
        "CHANNELS" : "32",
    },
    "64_channel_comb" : {
        "CHANNELS" : "64",
    },
    "opt_fifo_true" : {
        "OPTIONAL_TRBUF_FIFO" : "TRUE",
    },
    "_combinations_" : (
        (), # Works the same as '("default",),' as the "default" is applied in every combination
        ("16_channel_comb",),
        ("32_channel_comb",),
        ("64_channel_comb",),

        ("16_channel_comb","opt_fifo_true",),
        ("32_channel_comb","opt_fifo_true",),
        ("64_channel_comb","opt_fifo_true",),

        ("512bit_variant",),
        ("512bit_variant","16_channel_comb",),
        ("512bit_variant","32_channel_comb",),
        ("512bit_variant","64_channel_comb",),

        ("opt_fifo_true",),
        ("512bit_variant","opt_fifo_true",),
        ("512bit_variant","16_channel_comb","opt_fifo_true",),
        ("512bit_variant","32_channel_comb","opt_fifo_true",),
        ("512bit_variant","64_channel_comb","opt_fifo_true",),
    ),
}
