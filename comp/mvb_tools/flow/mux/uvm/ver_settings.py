# ver_settings.py
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Oliver Gurka <xgurka00@stud.fit.vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "MVB_ITEMS"         : "4",
        "DATA_WIDTH"        : "32",
        "MUX_WIDTH"         : "4",
    },
    "bus_comb_1" : {
        "DATA_WIDTH"        : "64",
    },
    "bus_comb_2" : {
        "DATA_WIDTH"        : "32",
    },
    "bus_comb_3" : {
        "DATA_WIDTH"        : "77",
    },
    "items_comb_1" : {
        "MVB_ITEMS"             : "8",
    },
    "items_comb_2" : {
        "MVB_ITEMS"             : "1",
    },
    "mux_comb_1": {
        "MUX_WIDTH"         : "8",
    },
    "mux_comb_2": {
        "MUX_WIDTH"         : "11",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination

    ("bus_comb_1",),
    ("bus_comb_2", "mux_comb_1"),
    ("bus_comb_3", "mux_comb_2"),

    ("items_comb_1",),
    ("items_comb_1","bus_comb_1", "mux_comb_1"),
    ("items_comb_2","bus_comb_2", "mux_comb_1"),

    ("items_comb_1", "bus_comb_3", "mux_comb_1"),
    ("items_comb_2", "bus_comb_3", "mux_comb_2"),
    ),
}
