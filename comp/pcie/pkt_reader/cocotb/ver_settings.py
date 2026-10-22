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

    # Cocotb test parameters (not VHDL generics).
    # Passed to the test as environment variables via __cocotb_params__.
    "frames_1000" : {
        "__cocotb_params__"     : {"FRAME_COUNT": "1000"},
    },
    "frames_2000" : {
        "__cocotb_params__"     : {"FRAME_COUNT": "2000"},
    },

    "_combinations_" : (
    # PCIe down MFB of P-Tile and R-Tile (default), UltraScale+ (4r_1b_4i) and R-Tile Gen5 (4r_1b_8i)
    ("frames_2000",),
    ("pcie_down_4r_1b_4i","frames_2000"),
    ("pcie_down_4r_1b_8i","user_mfb_1r_1b_16i","frames_1000"),
    ("pcie_down_1r_1b_8i","user_mfb_1r_1b_16i","mtu_max","frames_1000"),
    ("pcie_down_4r_1b_4i","mtu_127","no_fwft","frames_1000"),

    ("resp_out_of_order","pcie_down_4r_1b_8i","frames_1000"),
    ("resp_out_of_order","mtu_127","frames_1000"),
    ("resp_out_of_order","mtu_max","no_fwft","frames_1000"),

    ("fake_reader","frames_1000"),
    ("fake_reader","user_mfb_1r_1b_256i","mtu_max","frames_1000"),
    ),
}
