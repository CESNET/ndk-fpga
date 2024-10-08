# ver_settings.py
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Radek Iša <isa@cesnet.cz>

SETTINGS = {
    "default" : {
        "SIMULATION_DURATION" : "40ms" ,
        "CLK_PERIOD"          : "10ns" ,
        "RESET_TIME"          : "30*CLK_PERIOD" ,
        "DEVICE"              : "\\\"STRATIX10\\\"" ,
        "PCIE_DATA_WIDTH"     : "512" ,
        "MRRS"                : "512" ,
        "VERBOSE"             : "0" ,
        "MI_WIDTH"            : "32" ,
    },

    "device_stratix" : {
        "DEVICE"              : "\\\"STRATIX10\\\"" ,
        "PCIE_DATA_WIDTH"     : "512" ,
    },
    "device_ultrascale" : {
        "DEVICE"              : "\\\"ULTRASCALE\\\"" ,
        "PCIE_DATA_WIDTH"     : "512" ,
    },
    "short_simulatin" : {
        "SIMULATION_DURATION" : "20us",
    },
    "long_simulatin" : {
        "SIMULATION_DURATION" : "40ms",
    },
    "mi_32" : {
        "MI_WIDTH"            : "32" ,
    },
    "mi_64" : {
        "MI_WIDTH"            : "64" ,
    },
    "_combinations_" : (
        ("default", "device_stratix"),
        ("default", "device_ultrascale"),
#        ("default",  "mi_64"),
    )
}

