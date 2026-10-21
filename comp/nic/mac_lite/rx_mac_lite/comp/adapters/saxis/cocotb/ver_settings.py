# ver_settings.py: Generic combinations of the RX_MAC_LITE_ADAPTER_SAXIS cocotb test
# Copyright (C) 2026 DynaNIC Semiconductors, Ltd.
# Author(s): Vlastimil Kosar <kosar@dyna-nic.com>
#
# SPDX-License-Identifier: BSD-3-Clause

# REGION_SIZE follows SEGMENTS through its default value 2*SEGMENTS.
SETTINGS = {
    # 200G and 100G wide interface of the DCMAC, 512b
    "default" : {
        "SEGMENTS" : "4",
    },
    # 100G narrow interface of the DCMAC, 256b
    "segments_2" : {
        "SEGMENTS" : "2",
    },

    # Cocotb test parameters (not VHDL generics).
    "transactions_10000" : {
        "__cocotb_params__" : {"TRANSACTIONS": "10000"},
    },

    "_combinations_" : (
        ("segments_2",),
        ("transactions_10000",),
    ),
}
