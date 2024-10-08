# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "REGIONS"            : "4",
        "REGION_SIZE"        : "8",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
        "FAKE_PIPE"          : "0",
        "USE_DST_RDY"        : "1",
        "PIPE_TYPE"          : "\\\"SHREG\\\"",
        "DEVICE"             : "\\\"ULTRASCALE\\\"",
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
    "fake_pipe_up" : {
        "FAKE_PIPE"          : "1",
    },
    "use_dst_rdy_down" : {
        "USE_DST_RDY"        : "0",
    },
    "pipe_type_reg" : {
        "PIPE_TYPE"          : "\\\"REG\\\"",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("region_comb_1",),
    ("region_comb_2",),
    ("region_comb_3",),
    ("region_comb_4",),
    ("region_comb_5",),
    ("region_comb_6",),
    ("pcie",),

    ("fake_pipe_up",),
    ("use_dst_rdy_down",),
    ("pipe_type_reg",),

    ("pcie", "fake_pipe_up",),
    ("pcie", "use_dst_rdy_down",),

    ("region_comb_1", "fake_pipe_up",),

    ("region_comb_2", "fake_pipe_up",),

    ("region_comb_3", "fake_pipe_up",),
    ("region_comb_3", "use_dst_rdy_down",),

    ("region_comb_4", "fake_pipe_up",),

    ("region_comb_5", "fake_pipe_up",),
    ("region_comb_5", "use_dst_rdy_down",),

    ("region_comb_6", "fake_pipe_up",),
    ),
}
