# ver_settings.py
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification (512b variant without straddling)
        "MFB_REGIONS"     : "2"                 ,
        "MFB_REGION_SIZE" : "1"                 ,
        "MFB_BLOCK_SIZE"  : "8"                 ,
        "MFB_ITEM_WIDTH"  : "32"                ,
        "CC_TUSER_WIDTH"  : "81"                ,
        "STRADDLING"      : "0"                 ,
    },
    "axi_256b" : {
        "MFB_REGIONS"     : "1"                 ,
        "MFB_REGION_SIZE" : "1"                 ,
        "MFB_BLOCK_SIZE"  : "8"                 ,
        "MFB_ITEM_WIDTH"  : "32"                ,
        "CC_TUSER_WIDTH"  : "33"                ,
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("axi_256b",),
    ),
}
