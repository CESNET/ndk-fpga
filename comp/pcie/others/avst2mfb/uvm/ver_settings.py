# ver_settings.py
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification (512b variant without straddling)
        "REGIONS"         : "2"                 ,
        "REGION_SIZE"     : "1"                 ,
        "BLOCK_SIZE"      : "8"                 ,
        "ITEM_WIDTH"      : "32"                ,
        "META_WIDTH"      : "128"               ,
        "READY_LATENCY"   : "3"                 ,
        "FIFO_DEPTH"      : "32"                ,
        "FIFO_ENABLE"     : "1"                 ,
        "FIFO_RAM_TYPE"   : "\\\"AUTO\\\""      ,
        "DEVICE"          : "\\\"STRATIX10\\\"" ,
    },
    "avalon_256b" : {
        "REGIONS"     : "1"                 ,
    },
    "avalon_1024b" : {
        "REGIONS"     : "4"                 ,
    },
    "avalon_latency_27" : {
        "READY_LATENCY"   : "27"                 ,
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    (                "avalon_latency_27",),
    ("avalon_256b",                                            ),
    ("avalon_256b",  "avalon_latency_27",),
    ("avalon_1024b",                                           ),
    ("avalon_1024b", "avalon_latency_27",),
    ),
}
