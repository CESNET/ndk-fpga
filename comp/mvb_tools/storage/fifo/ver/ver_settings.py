# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "ITEMS"             : "4",
        "ITEM_WIDTH"        : "8",
        "USE_DST_RDY"       : "1",
        "USE_BRAMS"         : "0",
        "FIFO_ITEMS"        : "64",
        "OUTPUT_REG"        : "1",
        "TRANSACTION_COUNT" : "10000",
    },
    "bus_comb_1" : {
        "ITEM_WIDTH"        : "32",
    },
    "bus_comb_2" : {
        "ITEM_WIDTH"        : "77",
    },
    "items_comb_1" : {
        "ITEMS"             : "8",
    },
    "items_comb_2" : {
        "ITEMS"             : "1",
    },
    "use_dst_rdy_0" : {
        "USE_DST_RDY"       : "0",
    },
    "output_reg_0" : {
        "OUTPUT_REG"       : "0",
    },
    "use_brams_1" : {
        "USE_BRAMS"         : "1",
    },
    "fifo_items_1" : {
        "FIFO_ITEMS"        : "16",
    },
    "fifo_items_2" : {
        "FIFO_ITEMS"        : "2",
    },
    "fifo_items_3" : {
        "FIFO_ITEMS"        : "128",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("fifo_items_1",),
    ("fifo_items_2",),
    ("fifo_items_3",),
    ("output_reg_0",),

    ("bus_comb_1",),
    ("bus_comb_1","output_reg_0",),
    ("bus_comb_1","fifo_items_1",),
    ("bus_comb_1","fifo_items_2",),
    ("bus_comb_1","fifo_items_2","output_reg_0",),
    ("bus_comb_1","fifo_items_3",),
    ("bus_comb_1","fifo_items_3","use_brams_1"),

    ("bus_comb_2",),
    ("bus_comb_2","output_reg_0",),
    ("bus_comb_2","fifo_items_1",),
    ("bus_comb_2","fifo_items_2",),
    ("bus_comb_2","fifo_items_2","use_brams_1"),
    ("bus_comb_2","fifo_items_3",),

    ("items_comb_1","fifo_items_1",),
    ("items_comb_1","fifo_items_1","output_reg_0","use_brams_1"),
    ("items_comb_1","fifo_items_2",),
    ("items_comb_1","fifo_items_3",),

    ("items_comb_1","bus_comb_1","fifo_items_1",),
    ("items_comb_1","bus_comb_1","fifo_items_1","output_reg_0","use_brams_1",),
    ("items_comb_1","bus_comb_1","fifo_items_2",),
    ("items_comb_1","bus_comb_1","fifo_items_3",),

    ("items_comb_1","bus_comb_2","fifo_items_1",),
    ("items_comb_1","bus_comb_2","fifo_items_1","output_reg_0","use_brams_1",),
    ("items_comb_1","bus_comb_2","fifo_items_2",),
    ("items_comb_1","bus_comb_2","fifo_items_3",),

    ("items_comb_2","fifo_items_1",),
    ("items_comb_2","fifo_items_2",),
    ("items_comb_2","fifo_items_3",),

    ("items_comb_2","bus_comb_1","fifo_items_1",),
    ("items_comb_2","bus_comb_1","fifo_items_2",),
    ("items_comb_2","bus_comb_1","fifo_items_3",),

    ("items_comb_2","bus_comb_2","fifo_items_1",),
    ("items_comb_2","bus_comb_2","fifo_items_2",),
    ("items_comb_2","bus_comb_2","fifo_items_3",),
    ),
}
