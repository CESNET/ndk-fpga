# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "REGIONS"           : "4",
        "ITEM_WIDTH"        : "8",
        "FIFO_ITEMS"        : "1024",
        "TRANSACTION_COUNT" : "10000",
    },
    "bus_comb_1" : {
        "ITEM_WIDTH"        : "32",
    },
    "bus_comb_2" : {
        "ITEM_WIDTH"        : "77",
    },
    "items_comb_1" : {
        "REGIONS"             : "8",
    },
    "items_comb_2" : {
        "REGIONS"             : "1",
    },
    "fifo_items_1" : {
        "FIFO_ITEMS"        : "8192",
    },
    "fifo_items_2" : {
        "FIFO_ITEMS"        : "512",
    },
    "fifo_items_3" : {
        "FIFO_ITEMS"        : "2048",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("fifo_items_1",),
    ("fifo_items_2",),
    ("fifo_items_3",),

    ("bus_comb_1",),
    ("bus_comb_1","fifo_items_1",),
    ("bus_comb_1","fifo_items_2",),
    ("bus_comb_1","fifo_items_3",),

    ("bus_comb_2",),
    ("bus_comb_2","fifo_items_1",),
    ("bus_comb_2","fifo_items_2",),
    ("bus_comb_2","fifo_items_3",),

    ("items_comb_1","fifo_items_1",),
    ("items_comb_1","fifo_items_2",),
    ("items_comb_1","fifo_items_3",),

    ("items_comb_1","bus_comb_1","fifo_items_1",),
    ("items_comb_1","bus_comb_1","fifo_items_2",),
    ("items_comb_1","bus_comb_1","fifo_items_3",),

    ("items_comb_1","bus_comb_2","fifo_items_1",),
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
