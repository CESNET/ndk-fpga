# ver_settings.py
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification (512b variant without straddling)
        "MFB_REGIONS"     : "2"               ,
        "MFB_REGION_SIZE" : "1"               ,
        "MFB_BLOCK_SIZE"  : "8"               ,
        "MFB_ITEM_WIDTH"  : "32"              ,
        "META_WIDTH"      : "128"             ,
        "READY_LATENCY"   : "3"               ,
    },
    "avalon_256b" : {
        "MFB_REGIONS"     : "1"               ,
    },
    "avalon_1024b" : {
        "MFB_REGIONS"     : "4"               ,
    },
    "ready_latency_1" : { # R-Tile
        "READY_LATENCY"   : "1"               ,
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("avalon_256b",),
    ("avalon_1024b",),
    ("ready_latency_1",),
    ("avalon_1024b", "ready_latency_1",),
    ),
}
