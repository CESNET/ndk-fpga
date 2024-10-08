# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "REGIONS"            : "4",
        "REGION_SIZE"        : "8",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
        "ITEMS"              : "1024",
        "FRAME_SIZE_MAX"     : "512",
        "FRAME_SIZE_MIN"     : "60",
        "TRANSACTION_COUNT"  : "2000",
    },
    "pcie" : {
        "REGIONS"            : "2",
        "REGION_SIZE"        : "1",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "32",
    },
    "region_comb_1" : {
        "REGIONS"            : "1",
        "REGION_SIZE"        : "8",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
    },
    "region_comb_2" : {
        "REGIONS"            : "2",
        "REGION_SIZE"        : "8",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
    },
    "region_comb_3" : {
        "REGIONS"            : "1",
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
    "region_comb_5" : {
        "REGIONS"            : "1",
        "REGION_SIZE"        : "2",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
    },
    "region_comb_6" : {
        "REGIONS"            : "1",
        "REGION_SIZE"        : "4",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
    },
    "fifo_depth_comb_1" : {
        "ITEMS"              : "512",
    },
    "fifo_depth_comb_2" : {
        "ITEMS"              : "2048",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("fifo_depth_comb_1",),
    ("fifo_depth_comb_2",),

    ("pcie",),
    ("pcie","fifo_depth_comb_1",),
    ("pcie","fifo_depth_comb_2",),

    ("region_comb_1",),
    ("region_comb_1","fifo_depth_comb_1",),
    ("region_comb_1","fifo_depth_comb_2",),

    ("region_comb_2",),
    ("region_comb_2","fifo_depth_comb_1",),
    ("region_comb_2","fifo_depth_comb_2",),

    ("region_comb_3",),
    ("region_comb_3","fifo_depth_comb_1",),
    ("region_comb_3","fifo_depth_comb_2",),

    ("region_comb_4",),
    ("region_comb_4","fifo_depth_comb_1",),
    ("region_comb_4","fifo_depth_comb_2",),

    ("region_comb_5",),
    ("region_comb_5","fifo_depth_comb_1",),
    ("region_comb_5","fifo_depth_comb_2",),

    ("region_comb_6",),
    ("region_comb_6","fifo_depth_comb_1",),
    ("region_comb_6","fifo_depth_comb_2",),
    ),
}
