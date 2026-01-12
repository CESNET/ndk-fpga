# ver_settings.py
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification (512b variant without straddling)
        "MFB_REGIONS"     : "2"                 ,
        "MFB_REGION_SIZE" : "1"                 ,
        "MFB_BLOCK_SIZE"  : "8"                 ,
        "STRADDLING"      : "0"                 ,
    },
    "axi_256b" : {
        "MFB_REGIONS"     : "1"                 ,
        "MFB_REGION_SIZE" : "1"                 ,
        "MFB_BLOCK_SIZE"  : "8"                 ,
    },
    "straddling_on" : {
        "STRADDLING"      : "1"                 ,
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("default", "straddling_on"), # Works the same as '("default",),' as the "default" is applied in every combination
    ("axi_256b",),
    # NOT IMPLEMENTED
    #("axi_256b", "straddling_on"),
    ),
}
