# ver_settings.py
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification (512b variant with straddling)
        "MFB_REGIONS"     : "2"                 ,
        "MFB_REGION_SIZE" : "1"                 ,
        "MFB_BLOCK_SIZE"  : "8"                 ,
        "MFB_ITEM_WIDTH"  : "32"                ,
        "RQ_TUSER_WIDTH"  : "183"               ,
        "STRADDLING"      : "1"                 ,
        "DEVICE"          : "\\\"ULTRASCALE\\\"",
    },
    "axi_256b" : {
        "MFB_REGIONS"     : "1"                 ,
        "MFB_REGION_SIZE" : "1"                 ,
        "MFB_BLOCK_SIZE"  : "8"                 ,
        "MFB_ITEM_WIDTH"  : "32"                ,
        "RQ_TUSER_WIDTH"  : "88"                ,
        "STRADDLING"      : "0"                 ,
    },
    "axi_virtex" : {
        "RQ_TUSER_WIDTH"  : "85"                ,
        "DEVICE"          : "\\\"VIRTEX7\\\""   ,
    },
    "axi_straddling_off" : {
        "STRADDLING"      : "0"                 ,
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("axi_straddling_off"   ,),
    ("axi_256b"              ,),
    ("axi_256b", "axi_virtex",),
    ),
}
