# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Mikuláš Brázda <xbrazd21@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "REGIONS"            : "4",
        "REGION_SIZE"        : "8",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "16",
        "FIFO_DEPTH"         : "128",
    },
    "pcie" : {
        "REGIONS"            : "2",
        "REGION_SIZE"        : "1",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "32",
    },

    "region_comb_1" : {
        "REGIONS"            : "2",
        "REGION_SIZE"        : "4",
        "BLOCK_SIZE"         : "2",
        "ITEM_WIDTH"         : "8",
    },

    "region_comb_3" : {
        "REGIONS"            : "2",
        "REGION_SIZE"        : "1",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
    },
    "region_comb_4" : {
        "REGIONS"            : "1",
        "REGION_SIZE"        : "2",
        "BLOCK_SIZE"         : "4",
        "ITEM_WIDTH"         : "8",
    },

    "fifo_depth_comb_2" : {
        "FIFO_DEPTH"          : "1024",
    },
    "fifo_depth_comb_3" : {
        "FIFO_DEPTH"          : "42",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("fifo_depth_comb_2",),
    ("fifo_depth_comb_3",),

    ("pcie",),
    ("pcie","fifo_depth_comb_3",),

    ("region_comb_1",),
    ("region_comb_1","fifo_depth_comb_2",),

    ("region_comb_3",),
    ("region_comb_3","fifo_depth_comb_3",),

    ("region_comb_4",),
    ("region_comb_4","fifo_depth_comb_2",),
    ("region_comb_4","fifo_depth_comb_3",),

    ),
}
