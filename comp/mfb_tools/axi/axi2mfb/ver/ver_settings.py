# ver_settings.py:  Verification settings
# Copyright (C) 2024 BrnoLogic, Ltd.
# Author(s): Radek Hajek <hajek@brnologic.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    "default" : { # The default setting of verification
        "REGIONS"            : "1",
        "REGION_SIZE"        : "4",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
        "AXI_DATA_WIDTH"     : "256",
        "USE_IN_PIPE"        : "0",
        "USE_OUT_PIPE"       : "0",
    },
    "region_comb_1" : {
        "REGIONS"            : "1",
        "REGION_SIZE"        : "8",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
        "AXI_DATA_WIDTH"     : "512",
    },
    "region_comb_2" : {
        "REGIONS"            : "2",
        "REGION_SIZE"        : "8",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
        "AXI_DATA_WIDTH"     : "1024",
    },
    "region_comb_3" : {
        "REGIONS"            : "1",
        "REGION_SIZE"        : "1",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
        "AXI_DATA_WIDTH"     : "64",
    },
    "region_comb_4" : {
        "REGIONS"            : "1",
        "REGION_SIZE"        : "2",
        "BLOCK_SIZE"         : "4",
        "ITEM_WIDTH"         : "8",
        "AXI_DATA_WIDTH"     : "64",
    },
    "region_comb_5" : {
        "REGIONS"            : "4",
        "REGION_SIZE"        : "4",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
        "AXI_DATA_WIDTH"     : "1024",
    },
    "pipe_in" : {
        "USE_IN_PIPE"        : "1",
    },
    "pipe_out" : {
        "USE_OUT_PIPE"       : "1",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("pipe_in",),
    ("pipe_out",),
    ("pipe_in","pipe_out",),

    ("region_comb_1",),
    ("region_comb_2",),
    ("region_comb_3",),
    ("region_comb_4",),
    ("region_comb_5",),
    ("region_comb_5","pipe_in","pipe_out",),

    ),
}
