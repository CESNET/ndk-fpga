# ver_settings.py
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    # The default setting of verification. Only changed generics are listed.
    "default" : {
        "MFB_REGIONS"          : "1",
        "MFB_REGION_SIZE"      : "8",
        "MFB_BLOCK_SIZE"       : "8",
        "MFB_ITEM_WIDTH"       : "8",
        "PCIE_MFB_REGIONS"     : "2",
        "PCIE_MFB_REGION_SIZE" : "1",
        "PCIE_MFB_BLOCK_SIZE"  : "8",
        "PCIE_MFB_ITEM_WIDTH"  : "32",
        "AXI_RX_DIRECT"        : "True",
        "AXI_TDATA_WIDTH"      : "512",
        "PKT_MTU"              : "4096",
    },

    # PCIe MFB interface variants
    "pcie_mfb_1r_1b_8i" : {
        "PCIE_MFB_REGIONS"     : "1",
        "PCIE_MFB_REGION_SIZE" : "1",
        "PCIE_MFB_BLOCK_SIZE"  : "8",
        "PCIE_MFB_ITEM_WIDTH"  : "32",
    },
    "pcie_mfb_4r_1b_4i" : {
        "PCIE_MFB_REGIONS"     : "4",
        "PCIE_MFB_REGION_SIZE" : "1",
        "PCIE_MFB_BLOCK_SIZE"  : "4",
        "PCIE_MFB_ITEM_WIDTH"  : "32",
    },
    "pcie_mfb_4r_1b_8i" : {
        "PCIE_MFB_REGIONS"     : "4",
        "PCIE_MFB_REGION_SIZE" : "1",
        "PCIE_MFB_BLOCK_SIZE"  : "8",
        "PCIE_MFB_ITEM_WIDTH"  : "32",
    },

    # MFB input instead of the default AXI4-Stream input
    "rx_via_mfb" : {
        "AXI_RX_DIRECT"        : "False",
    },

    # Wider AXI4-Stream input
    "wide_rx_axi" : {
        "AXI_TDATA_WIDTH"      : "2048",
    },

    # Wider MFB input
    "wide_rx_mfb" : {
        "MFB_REGIONS"          : "1",
        "MFB_REGION_SIZE"      : "1",
        "MFB_BLOCK_SIZE"       : "256",
        "MFB_ITEM_WIDTH"       : "8",
        "AXI_RX_DIRECT"        : "False",
    },

    # Packet MTU variants
    "mtu_127" : {
        "PKT_MTU"              : "127",
    },
    "mtu_max" : {
        "PKT_MTU"              : "16383",
    },

    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination

    ("pcie_mfb_1r_1b_8i",),
    ("pcie_mfb_4r_1b_4i",),
    ("pcie_mfb_4r_1b_8i",),
    ("mtu_127",),
    ("mtu_max",),

    ("rx_via_mfb",),
    ("rx_via_mfb","pcie_mfb_4r_1b_8i"),
    ("rx_via_mfb","mtu_127"),

    ("pcie_mfb_1r_1b_8i","mtu_max"),
    ("pcie_mfb_4r_1b_4i","mtu_127"),

    ("wide_rx_axi","mtu_max"),

    ("wide_rx_mfb",),
    ("wide_rx_mfb","pcie_mfb_4r_1b_8i","mtu_max"),

    ),
}
