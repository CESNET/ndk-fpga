# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "ITEMS"             : "4",
        "ITEM_WIDTH"        : "8",
        "IMPLEMENTATION"    : "\\\"serial\\\"",
        "TRANSACTION_COUNT" : "10000",
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
    "version_parallel" : {
        "IMPLEMENTATION"    : "\\\"parallel\\\"",
    },
    "version_prefixsum" : {
        "IMPLEMENTATION"    : "\\\"prefixsum\\\"",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination

    ("version_parallel",),
    ("version_prefixsum",),

    ("items_comb_1",),
    ("items_comb_1","version_parallel",),
    ("items_comb_1","version_prefixsum",),

    ("items_comb_2","version_parallel",),
    ("items_comb_2","version_prefixsum",),
    ("items_comb_2",),

    ("bus_comb_1","version_parallel",),
    ("bus_comb_1","version_prefixsum",),
    ("bus_comb_1",),

    ("bus_comb_1","items_comb_1","version_parallel",),
    ("bus_comb_1","items_comb_1","version_prefixsum",),
    ("bus_comb_1","items_comb_1",),

    ("bus_comb_1","items_comb_2","version_parallel",),
    ("bus_comb_1","items_comb_2","version_prefixsum",),
    ("bus_comb_1","items_comb_2",),

    ("bus_comb_2","version_parallel",),
    ("bus_comb_2","version_prefixsum",),
    ("bus_comb_2",),

    ("bus_comb_2","items_comb_1","version_parallel",),
    ("bus_comb_2","items_comb_1","version_prefixsum",),
    ("bus_comb_2","items_comb_1",),

    ("bus_comb_2","items_comb_2","version_parallel",),
    ("bus_comb_2","items_comb_2","version_prefixsum",),
    ("bus_comb_2","items_comb_2",),
    ),
}
