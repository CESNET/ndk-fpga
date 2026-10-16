# ver_settings.py: Generic combinations of the AXI4LITE2MI cocotb test
# Copyright (C) DynaNIC Semiconductors, Ltd.
# Author(s): Vlastimil Kosar <kosar@dyna-nic.com>, 2026
#
# SPDX-License-Identifier: BSD-3-Clause

# The tests read ADDR_WIDTH and ADDR_MASK from the DUT, so every combination is
# checked against its own address mapping. DATA_WIDTH must stay 32.
SETTINGS = {
    "default" : {
        "ADDR_WIDTH" : "32",
    },

    "addr_width_16" : {
        "ADDR_WIDTH" : "16",
    },
    "addr_width_12" : {
        "ADDR_WIDTH" : "12",
    },

    # Cocotb test parameters (not VHDL generics).
    "transactions_10000" : {
        "__cocotb_params__" : {"TRANSACTIONS": "10000"},
    },

    "_combinations_" : (
        ("addr_width_16",),
        ("addr_width_12",),
        ("transactions_10000",),
    ),
}
