# ver_settings.py: generic combinations of the MFB_SPEED_METER_MI cocotb test
# Copyright (C) 2026 Universitaet Heidelberg, Institut fuer Technische Informatik (ZITI)
# Author(s): Vladislav Valek <vladislav.valek@stud.uni-heidelberg.de>
#
# SPDX-License-Identifier: Apache-2.0

SETTINGS = {
    # The default setting of verification. Only changed generics are listed.
    "default": {
        "REGIONS": "2",
        "REGION_SIZE": "8",
        "BLOCK_SIZE": "8",
        "ITEM_WIDTH": "8",
        "CNT_TICKS_WIDTH": "24",
        "CNT_BYTES_WIDTH": "32",
        "CNT_PKTS_WIDTH": "32",
        "MI_DATA_WIDTH": "32",
    },

    "bytes_48": {
        "CNT_BYTES_WIDTH": "48",
    },

    "mi_8_bytes_16": {
        "CNT_BYTES_WIDTH": "16",
        "CNT_PKTS_WIDTH": "8",
        "MI_DATA_WIDTH": "8",
    },

    "mi_8_bytes_8": {
        "CNT_BYTES_WIDTH": "8",
        "CNT_PKTS_WIDTH": "8",
        "MI_DATA_WIDTH": "8",
    },

    "_combinations_": (
        (),
        ("bytes_48",),
        ("mi_8_bytes_16",),
        ("mi_8_bytes_8",),
    ),
}
