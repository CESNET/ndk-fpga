# ver_settings.py: generic combinations of the MFB_GENERATOR cocotb test
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
        "LENGTH_WIDTH": "16",
        "CHANNELS_WIDTH": "4",
        "PKT_CNT_WIDTH": "32",
        "USE_PACP_ARCH": "true",
        "DEVICE": "\\\"ULTRASCALE\\\"",
    },

    "core_arch": {
        "USE_PACP_ARCH": "false",
    },

    "block_32b": {
        "BLOCK_SIZE": "4",
    },

    "block_128b": {
        "BLOCK_SIZE": "16",
    },

    "_combinations_": (
        (),
        ("core_arch",),
        ("block_32b",),
        ("block_32b", "core_arch"),
        ("block_128b", "core_arch"),
    ),
}
