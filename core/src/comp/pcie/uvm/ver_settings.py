# ver_settings.py
# Copyright (C) 2023 CESNET z. s. p. o.
# Author(s): Daniel Kříž <danielkriz@cesnet.cz>

SETTINGS = {
    "default" : { # The default setting of verification is 512b and STRATIX with P_TILE
        "RQ_MFB_REGIONS"       : "2"                 ,
        "RQ_MFB_REGION_SIZE"   : "1"                 ,
        "RQ_MFB_BLOCK_SIZE"    : "8"                 ,

        "RC_MFB_REGIONS"       : "2"                 ,
        "RC_MFB_REGION_SIZE"   : "1"                 ,
        "RC_MFB_BLOCK_SIZE"    : "8"                 ,

        "CQ_MFB_REGIONS"       : "2"                 ,
        "CQ_MFB_REGION_SIZE"   : "1"                 ,
        "CQ_MFB_BLOCK_SIZE"    : "8"                 ,

        "CC_MFB_REGIONS"       : "2"                 ,
        "CC_MFB_REGION_SIZE"   : "1"                 ,
        "CC_MFB_BLOCK_SIZE"    : "8"                 ,

        "AXI_CQUSER_WIDTH"     : "183"               ,
        "AXI_CCUSER_WIDTH"     : "81"                ,
        "AXI_RQUSER_WIDTH"     : "137"               ,
        "AXI_RCUSER_WIDTH"     : "161"               ,
        "AXI_STRADDLING"       : "0"                 ,

        "DMA_PORTS"            : 1,
        "PCIE_ENDPOINT_MODE"   : 0,
        "PCIE_ENDPOINTS"       : 1,
        "PCIE_CONS"            : 1,

        "DEVICE"               : "\\\"AGILEX\\\"" ,
        "PCIE_ENDPOINT_TYPE"   : "\\\"P_TILE\\\""    ,
        "__core_params__"          : {"PCIE_TYPE" : "P_TILE"},
    },
    "intel_p_tile_512" : {
        "RQ_MFB_REGIONS"       : "2"                 ,
        "RQ_MFB_REGION_SIZE"   : "1"                 ,
        "RQ_MFB_BLOCK_SIZE"    : "8"                 ,

        "RC_MFB_REGIONS"       : "2"                 ,
        "RC_MFB_REGION_SIZE"   : "1"                 ,
        "RC_MFB_BLOCK_SIZE"    : "8"                 ,

        "CQ_MFB_REGIONS"       : "2"                 ,
        "CQ_MFB_REGION_SIZE"   : "1"                 ,
        "CQ_MFB_BLOCK_SIZE"    : "8"                 ,

        "CC_MFB_REGIONS"       : "2"                 ,
        "CC_MFB_REGION_SIZE"   : "1"                 ,
        "CC_MFB_BLOCK_SIZE"    : "8"                 ,

        "PCIE_ENDPOINT_MODE"   : 0,
        "PCIE_ENDPOINTS"       : 1,
        "PCIE_CONS"            : 1,
        "DMA_PORTS"            : 2,

        "DEVICE"               : "\\\"AGILEX\\\"" ,
        "PCIE_ENDPOINT_TYPE"   : "\\\"P_TILE\\\""    ,
        "__core_params__"          : {"PCIE_TYPE" : "P_TILE"},
    },
    "intel_p_tile_256_bif" : {
        "RQ_MFB_REGIONS"       : "2"                 ,
        "RQ_MFB_REGION_SIZE"   : "1"                 ,
        "RQ_MFB_BLOCK_SIZE"    : "8"                 ,

        "RC_MFB_REGIONS"       : "2"                 ,
        "RC_MFB_REGION_SIZE"   : "1"                 ,
        "RC_MFB_BLOCK_SIZE"    : "8"                 ,

        "CQ_MFB_REGIONS"       : "1"                 ,
        "CQ_MFB_REGION_SIZE"   : "1"                 ,
        "CQ_MFB_BLOCK_SIZE"    : "8"                 ,

        "CC_MFB_REGIONS"       : "1"                 ,
        "CC_MFB_REGION_SIZE"   : "1"                 ,
        "CC_MFB_BLOCK_SIZE"    : "8"                 ,

        "PCIE_ENDPOINT_MODE"   : 1,
        "PCIE_ENDPOINTS"       : 2,
        "PCIE_CONS"            : 1,
        "DMA_PORTS"            : 1,

        "DEVICE"               : "\\\"AGILEX\\\"" ,
        "PCIE_ENDPOINT_TYPE"   : "\\\"P_TILE\\\""    ,
        "__core_params__"          : {"PCIE_TYPE" : "P_TILE"},
    },
    "intel_r_tile_1024" : {
        "RQ_MFB_REGIONS"       : "2",
        "RQ_MFB_REGION_SIZE"   : "1",
        "RQ_MFB_BLOCK_SIZE"    : "8",

        "RC_MFB_REGIONS"       : "2",
        "RC_MFB_REGION_SIZE"   : "1",
        "RC_MFB_BLOCK_SIZE"    : "8",

        "CQ_MFB_REGIONS"       : "4",
        "CQ_MFB_REGION_SIZE"   : "1",
        "CQ_MFB_BLOCK_SIZE"    : "8",

        "CC_MFB_REGIONS"       : "4",
        "CC_MFB_REGION_SIZE"   : "1",
        "CC_MFB_BLOCK_SIZE"    : "8",

        "PCIE_ENDPOINT_MODE"   : 0,
        "PCIE_ENDPOINTS"       : 1,
        "PCIE_CONS"            : 1,
        "DMA_PORTS"            : 4,

        "DEVICE"               : "\\\"AGILEX\\\"",
        "PCIE_ENDPOINT_TYPE"   : "\\\"R_TILE\\\"",
        "__core_params__"      : {"PCIE_TYPE" : "R_TILE"},
    },
    "intel_r_tile_512_bif" : {
        "RQ_MFB_REGIONS"       : "2",
        "RQ_MFB_REGION_SIZE"   : "1",
        "RQ_MFB_BLOCK_SIZE"    : "8",

        "RC_MFB_REGIONS"       : "2",
        "RC_MFB_REGION_SIZE"   : "1",
        "RC_MFB_BLOCK_SIZE"    : "8",

        "CQ_MFB_REGIONS"       : "2",
        "CQ_MFB_REGION_SIZE"   : "1",
        "CQ_MFB_BLOCK_SIZE"    : "8",

        "CC_MFB_REGIONS"       : "2",
        "CC_MFB_REGION_SIZE"   : "1",
        "CC_MFB_BLOCK_SIZE"    : "8",

        "PCIE_ENDPOINT_MODE"   : 1,
        "PCIE_ENDPOINTS"       : 2,
        "PCIE_CONS"            : 1,
        "DMA_PORTS"            : 2,

        "DEVICE"               : "\\\"AGILEX\\\"",
        "PCIE_ENDPOINT_TYPE"   : "\\\"R_TILE\\\"",
        "__core_params__"      : {"PCIE_TYPE" : "R_TILE"},
    },
    "intel_r_tile_512_bif_2cons" : {
        "RQ_MFB_REGIONS"       : "2",
        "RQ_MFB_REGION_SIZE"   : "1",
        "RQ_MFB_BLOCK_SIZE"    : "8",

        "RC_MFB_REGIONS"       : "2",
        "RC_MFB_REGION_SIZE"   : "1",
        "RC_MFB_BLOCK_SIZE"    : "8",

        "CQ_MFB_REGIONS"       : "2",
        "CQ_MFB_REGION_SIZE"   : "1",
        "CQ_MFB_BLOCK_SIZE"    : "8",

        "CC_MFB_REGIONS"       : "2",
        "CC_MFB_REGION_SIZE"   : "1",
        "CC_MFB_BLOCK_SIZE"    : "8",

        "PCIE_ENDPOINT_MODE"   : 1,
        "PCIE_ENDPOINTS"       : 4,
        "PCIE_CONS"            : 2,
        "DMA_PORTS"            : 1,

        "DEVICE"               : "\\\"AGILEX\\\"",
        "PCIE_ENDPOINT_TYPE"   : "\\\"R_TILE\\\"",
        "__core_params__"      : {"PCIE_TYPE" : "R_TILE"},
    },

    "xilinx_usp_512" : {
        "RQ_MFB_REGIONS"       : "2"                 ,
        "RQ_MFB_REGION_SIZE"   : "1"                 ,
        "RQ_MFB_BLOCK_SIZE"    : "8"                 ,

        "RC_MFB_REGIONS"       : "4"                 ,
        "RC_MFB_REGION_SIZE"   : "1"                 ,
        "RC_MFB_BLOCK_SIZE"    : "4"                 ,

        "CQ_MFB_REGIONS"       : "2"                 ,
        "CQ_MFB_REGION_SIZE"   : "1"                 ,
        "CQ_MFB_BLOCK_SIZE"    : "8"                 ,

        "CC_MFB_REGIONS"       : "2"                 ,
        "CC_MFB_REGION_SIZE"   : "1"                 ,
        "CC_MFB_BLOCK_SIZE"    : "8"                 ,


        "AXI_CQUSER_WIDTH"     : "183"               ,
        "AXI_CCUSER_WIDTH"     : "81"                ,
        "AXI_RQUSER_WIDTH"     : "137"               ,
        "AXI_RCUSER_WIDTH"     : "161"               ,
        "AXI_STRADDLING"       : "0"                 ,

        "DEVICE"               : "\\\"ULTRASCALE\\\"",
        "PCIE_ENDPOINT_TYPE"   : "\\\"DUMMY\\\""     ,
        "__core_params__"          : {"PCIE_TYPE" : "USP"}     ,
    },

    "dma_ports_2" : {
        "DMA_PORTS"            : 2,
    },
    
    "_combinations_" : {
        "P_TILE_512"           : ("intel_p_tile_512",              ),
        "P_TILE_256_BIF"       : ("intel_p_tile_256_bif",          ),
        "R_TILE_1024"          : ("intel_r_tile_1024",             ),
        "R_TILE_512_BIF"       : ("intel_r_tile_512_bif",          ),
        "R_TILE_512_BIF_2CONS" : ("intel_r_tile_512_bif_2cons",    ),
        "USP_512"              : ("xilinx_usp_512",                ),
        "USP_512_DMA_2"        : ("xilinx_usp_512", "dma_ports_2", ),
    },
}
