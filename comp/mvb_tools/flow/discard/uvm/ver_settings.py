# ver_settings.py
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "ITEMS"             : "4",
        "ITEM_WIDTH"        : "8",
    },
    "bus_comb_1" : {
        "ITEM_WIDTH"        : "64",
    },
    "bus_comb_2" : {
        "ITEM_WIDTH"        : "32",
    },
    "bus_comb_3" : {
        "ITEM_WIDTH"        : "77",
    },
    "items_comb_1" : {
        "ITEMS"             : "8",
    },
    "items_comb_2" : {
        "ITEMS"             : "1",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination

    ("bus_comb_1",),
    ("bus_comb_2",),
    ("bus_comb_3",),

    ("items_comb_1",),
    ("items_comb_1","bus_comb_1",),
    ("items_comb_1","bus_comb_2",),
    ("items_comb_1","bus_comb_3",),

    ("items_comb_2",),
    ("items_comb_2","bus_comb_2",),
    ("items_comb_2","bus_comb_3",),
    ),
}
