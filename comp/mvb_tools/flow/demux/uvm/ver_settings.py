# ver_settings.py
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Oliver Gurka <xgurka00@stud.fit.vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "ITEMS"         : "4",
        "ITEM_WIDTH"    : "8",
        "TX_PORTS"      : "4",
        "DEMUX_VERSION" : "\\\"register\\\"",
        "OUTPUT_REG_EN" : "1",
    },
    "bus_comb_1" : {
        "TX_PORTS"      : "16",
        "ITEM_WIDTH"    : "64",
    },
    "bus_comb_2" : {
        "TX_PORTS"      : "8",
        "ITEM_WIDTH"    : "32",
    },
    "bus_comb_3" : {
        "TX_PORTS"      : "4",
        "ITEM_WIDTH"    : "77"
    },
    "items_comb_1" : {
        "ITEMS"         : "8"
    },
    "items_comb_2" : {
        "ITEMS"         : "16"
    },
    "logic_variant" : {
        "DEMUX_VERSION" : "\\\"logic\\\"",
        "OUTPUT_REG_EN" : "0"
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination

    ("bus_comb_1", "items_comb_1"),
    ("bus_comb_1", "items_comb_2"),
    ("bus_comb_2",                 "logic_variant"),
    ("bus_comb_2", "items_comb_1"),
    ("bus_comb_2", "items_comb_2"),
    ("bus_comb_3", "items_comb_2", "logic_variant")

    # ("bus_comb_1", "items_comb_1", "logic_variant"),
    # ("bus_comb_1", "items_comb_2", "logic_variant"),
    # ("bus_comb_2"                , "logic_variant"),
    # ("bus_comb_2", "items_comb_1", "logic_variant"),
    # ("bus_comb_2", "items_comb_2", "logic_variant"),
    ),
}
