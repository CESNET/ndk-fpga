# ver_settings.py
# Copyright (C) 2026 CESNET z. s. p. o.
# Author(s): Daniel Kondys <kondys@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    # The default setting of verification. Only changed generics are listed.
    "default" : {
        "REGIONS"               : "1",
        "REGION_SIZE"           : "8",
        "BLOCK_SIZE"            : "8",
        "ITEM_WIDTH"            : "8",
        "PCIE_DOWN_REGIONS"     : "2",
        "PCIE_DOWN_REGION_SIZE" : "1",
        "PCIE_DOWN_BLOCK_SIZE"  : "8",
        "PCIE_DOWN_ITEM_WIDTH"  : "32",
        "FAKE_READER"           : "False",
        "PKT_MTU"               : "4096",
        "RESP_IN_ORDER"         : "True",
        "FWFT"                  : "True",
    },

    # PCIe down MFB interface variants
    "pcie_down_1r_1b_8i" : {
        "PCIE_DOWN_REGIONS"     : "1",
        "PCIE_DOWN_REGION_SIZE" : "1",
        "PCIE_DOWN_BLOCK_SIZE"  : "8",
        "PCIE_DOWN_ITEM_WIDTH"  : "32",
    },
    "pcie_down_4r_1b_4i" : {
        "PCIE_DOWN_REGIONS"     : "4",
        "PCIE_DOWN_REGION_SIZE" : "1",
        "PCIE_DOWN_BLOCK_SIZE"  : "4",
        "PCIE_DOWN_ITEM_WIDTH"  : "32",
    },
    "pcie_down_4r_1b_8i" : {
        "PCIE_DOWN_REGIONS"     : "4",
        "PCIE_DOWN_REGION_SIZE" : "1",
        "PCIE_DOWN_BLOCK_SIZE"  : "8",
        "PCIE_DOWN_ITEM_WIDTH"  : "32",
    },

    # Packet MTU variants
    "mtu_127" : {
        "PKT_MTU"               : "127",
    },
    "mtu_max" : {
        "PKT_MTU"               : "16383",
    },

    # Output responses as they complete, ignoring the request order
    "resp_out_of_order" : {
        "RESP_IN_ORDER"         : "False",
    },

    # Disable First Word Fall Through on USER_RESP interface
    "no_fwft" : {
        "FWFT"                  : "False",
    },

    # Fake reader variant: generates empty packets of given length (PCIe interfaces not used)
    "fake_reader" : {
        "FAKE_READER"           : "True",
    },

    # USER MFB interface variant narrower than a single PCIE_DOWN region
    "user_mfb_1r_1b_16i" : {
        "REGIONS"               : "1",
        "REGION_SIZE"           : "1",
        "BLOCK_SIZE"            : "16",
        "ITEM_WIDTH"            : "8",
    },

    # USER MFB interface variant for 2048 wide words and SOF-aligned (AXI-like) frames
    "user_mfb_1r_1b_256i" : {
        "REGIONS"               : "1",
        "REGION_SIZE"           : "1",
        "BLOCK_SIZE"            : "256",
        "ITEM_WIDTH"            : "8",
    },

    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination

    ("pcie_down_1r_1b_8i",),
    ("pcie_down_4r_1b_4i",),
    ("pcie_down_4r_1b_8i","user_mfb_1r_1b_16i"),
    ("mtu_127",),
    ("mtu_max",),

    ("resp_out_of_order",),
    ("resp_out_of_order","pcie_down_4r_1b_8i"),
    ("resp_out_of_order","mtu_127"),
    ("resp_out_of_order","mtu_max","no_fwft"),

    ("pcie_down_1r_1b_8i","user_mfb_1r_1b_16i","mtu_max"),
    ("pcie_down_4r_1b_4i","mtu_127","no_fwft"),

    ("pcie_down_4r_1b_4i","resp_out_of_order","mtu_max"),

    ("fake_reader"),
    ("fake_reader","user_mfb_1r_1b_256i","mtu_max"),

    ),
}
