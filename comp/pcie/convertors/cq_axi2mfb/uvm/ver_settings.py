# ver_settings.py
# Copyright (C) 2022 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification (512b variant with straddling)
        "MFB_REGIONS"     : "2"                 ,
        "MFB_REGION_SIZE" : "1"                 ,
        "MFB_BLOCK_SIZE"  : "8"                 ,
        "STRADDLING"      : "1"                 ,
        "DEVICE"          : "\\\"ULTRASCALE\\\"",
    },
    "axi_256b" : {
        "MFB_REGIONS"     : "1"                 ,
        "MFB_REGION_SIZE" : "1"                 ,
        "MFB_BLOCK_SIZE"  : "8"                 ,
        "STRADDLING"      : "0"                 ,
    },
    "axi_straddling_off" : {
        "STRADDLING"      : "0"                 ,
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("axi_straddling_off"   ,),
    ("axi_256b"              ,),
    ),
}
