# ver_settings.py
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "RX0_ITEMS"         : "8",
        "RX0_ITEM_WIDTH"    : "32",
        "RX1_ITEMS"         : "8",
        "RX1_ITEM_WIDTH"    : "40",
        "RX0_FIFO_EN"       : "0",
        "FIFO_DEPTH"        : "32",
        "OUTPUT_REG"        : "0",
        "DEVICE"            : "\\\"STRATIX10\\\"",
    },
    "items_comb_11" : {
        "RX0_ITEMS"         : "1",
    },
    "items_comb_12" : {
        "RX0_ITEMS"         : "63",
    },
    "items_comb_21" : {
        "RX1_ITEMS"         : "1",
    },
    "items_comb_22" : {
        "RX1_ITEMS"         : "63",
    },
    "item_width_comb_1" : {
        "RX0_ITEM_WIDTH"    : "70",
    },
    "item_width_comb_2" : {
        "RX1_ITEM_WIDTH"    : "72",
    },
    "fifo_depth_comb_1" : {
        "FIFO_DEPTH"        : "2",
    },
    "fifo_depth_comb_2" : {
        "FIFO_DEPTH"        : "512",
    },
    "fifo_depth_comb_3" : {
        "FIFO_DEPTH"        : "4200",
    },
    "enable_input_fifo" : {
        "RX0_FIFO_EN"       : "1",
    },
    "enable_output_fifo" : {
        "OUTPUT_REG"        : "1",
    },
    "device_comb_1" : {
        "DEVICE"            : "\\\"7SERIES\\\"",
    },
    "device_comb_2" : {
        "DEVICE"            : "\\\"ARRIA10\\\"",
    },
    "device_comb_3" : {
        "DEVICE"            : "\\\"ULTRASCALE\\\"",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination

    ("items_comb_12", "item_width_comb_1",),

    ("items_comb_11", "items_comb_21", "item_width_comb_1", "enable_output_fifo",),

    ("items_comb_12", "items_comb_22", "item_width_comb_2", "enable_output_fifo", "fifo_depth_comb_3", "device_comb_1",),
    ("items_comb_12", "items_comb_22", "item_width_comb_2", "enable_output_fifo", "fifo_depth_comb_3", "device_comb_3",),
    ("items_comb_12", "items_comb_22", "enable_output_fifo", "fifo_depth_comb_3", "device_comb_3",),

    ("items_comb_11", "items_comb_22", "item_width_comb_2",  "enable_input_fifo", "fifo_depth_comb_2", "device_comb_1",),
    ("items_comb_12", "items_comb_21", "enable_output_fifo", "enable_input_fifo", "fifo_depth_comb_1", "device_comb_2",),
    ("items_comb_12", "items_comb_22", "item_width_comb_1",  "enable_input_fifo", "fifo_depth_comb_2", "device_comb_3",),

    ("items_comb_12", "items_comb_22", "item_width_comb_1",  "enable_input_fifo", "fifo_depth_comb_2", "device_comb_1",),
    ("items_comb_11", "items_comb_22", "item_width_comb_1",  "enable_input_fifo", "fifo_depth_comb_3", "device_comb_3",),

    ),
}
