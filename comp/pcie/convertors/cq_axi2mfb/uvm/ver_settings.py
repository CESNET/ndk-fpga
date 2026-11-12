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
    # Versal CPM5: the AXI_CQUSER_WIDTH is 231 (512b) or 465 (1024b)
    "versal" : {
        "DEVICE"          : "\\\"VERSAL\\\""    ,
    },
    "axi_1024b" : {
        "MFB_REGIONS"     : "4"                 ,
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("axi_straddling_off"   ,),
    ("axi_256b"              ,),
    # The NDK does not use the Versal straddling (PCIE_CORE_AXI_COMMON has AXI_STRADDLING => false),
    # these combinations are its only verification. The Versal variants without straddling are
    # verified with the PCIE_MOD (core/comp/pcie/pcie_mod/uvm).
    ("versal"                ,),
    ("versal", "axi_1024b"   ,),
    ),
}
