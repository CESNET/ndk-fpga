# ver_settings.py: Generic combinations of the VERSAL_PS_CTRL cocotb test
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2026
#
# SPDX-License-Identifier: BSD-3-Clause

# The tests read the widths and AXI_ADDR_WIDTH_INT from the DUT, so every
# combination is checked against its own address translation.
SETTINGS = {
    # PS Slave AXI LPD interface
    "default" : {
        "AXI_ADDR_WIDTH_INT" : "32",
        "AXI_ADDR_WIDTH"     : "49",
        "AXI_ID_WIDTH"       : "6",
        "AXI_ARUSER_WIDTH"   : "10",
        "AXI_AWUSER_WIDTH"   : "10",
    },

    # Access through the NoC, the upper address bits are truncated to AXI_ADDR_WIDTH
    "noc" : {
        "AXI_ADDR_WIDTH_INT" : "64",
    },
    "noc_addr_64" : {
        "AXI_ADDR_WIDTH_INT" : "64",
        "AXI_ADDR_WIDTH"     : "64",
    },
    "noc_addr_40" : {
        "AXI_ADDR_WIDTH_INT" : "64",
        "AXI_ADDR_WIDTH"     : "40",
    },
    "addr_32" : {
        "AXI_ADDR_WIDTH"     : "32",
    },

    "id_width_1" : {
        "AXI_ID_WIDTH"       : "1",
    },
    "id_width_8" : {
        "AXI_ID_WIDTH"       : "8",
    },
    "user_width_16" : {
        "AXI_ARUSER_WIDTH"   : "16",
        "AXI_AWUSER_WIDTH"   : "16",
    },

    # Cocotb test parameters (not VHDL generics).
    "transactions_10000" : {
        "__cocotb_params__" : {"TRANSACTIONS": "10000"},
    },

    "_combinations_" : (
        ("noc",),
        ("noc_addr_64",),
        ("noc_addr_40",),
        ("addr_32",),
        ("id_width_1",),
        ("id_width_8", "user_width_16"),
        ("transactions_10000",),
    ),
}
