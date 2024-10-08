# ver_settings.py
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification (512b variant without straddling)
        "REGIONS"         : "2"                 ,
        "REGION_SIZE"     : "1"                 ,
        "BLOCK_SIZE"      : "8"                 ,
        "ITEM_WIDTH"      : "32"                ,
        "META_WIDTH"      : "128"               ,
    },
    "avalon_256b" : {
        "REGIONS"         : "1"                 ,
    },
    "avalon_1024b" : {
        "REGIONS"         : "4"                 ,
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("avalon_256b",),
    ("avalon_1024b",),
    ),
}
