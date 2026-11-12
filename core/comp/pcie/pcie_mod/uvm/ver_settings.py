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

        "STRADDLING"       : "0"                 ,

        "DMA_BAR_ENABLE"       : 0,
        "DMA_PORTS"            : 1,
        "PCIE_ENDPOINT_MODE"   : 0,
        "PCIE_ENDPOINTS"       : 1,
        "PCIE_CONS"            : 1,
        "PCIE_GEN"             : 4,

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
        "PCIE_GEN"             : 5,
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
        "PCIE_GEN"             : 5,
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
        "PCIE_GEN"             : 5,
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

        "STRADDLING"       : "0"                 ,

        "DEVICE"               : "\\\"ULTRASCALE\\\"",
        "PCIE_ENDPOINT_TYPE"   : "\\\"DUMMY\\\""     ,
        "__core_params__"          : {"PCIE_TYPE" : "USP"}     ,
    },
    # Versal CPM5 Gen3x16: 512b AXI interfaces of the PCIe IP core
    "xilinx_versal_512" : {
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

        "STRADDLING"           : "0"                 ,

        "PCIE_ENDPOINT_MODE"   : 0,
        "PCIE_ENDPOINTS"       : 1,
        "PCIE_CONS"            : 1,
        "PCIE_GEN"             : 3,
        "DMA_PORTS"            : 2,

        "DEVICE"               : "\\\"VERSAL\\\""    ,
        "PCIE_ENDPOINT_TYPE"   : "\\\"VERSAL\\\""    ,
        "__core_params__"      : {"PCIE_TYPE" : "VERSAL"},
    },
    # Versal CPM5 Gen4x16: 1024b AXI interfaces of the PCIe IP core,
    # the PTC converts the RQ and RC to the 512b DMA streams
    "xilinx_versal_1024" : {
        "RQ_MFB_REGIONS"       : "2"                 ,
        "RQ_MFB_REGION_SIZE"   : "1"                 ,
        "RQ_MFB_BLOCK_SIZE"    : "8"                 ,

        "RC_MFB_REGIONS"       : "4"                 ,
        "RC_MFB_REGION_SIZE"   : "1"                 ,
        "RC_MFB_BLOCK_SIZE"    : "4"                 ,

        "CQ_MFB_REGIONS"       : "4"                 ,
        "CQ_MFB_REGION_SIZE"   : "1"                 ,
        "CQ_MFB_BLOCK_SIZE"    : "8"                 ,

        "CC_MFB_REGIONS"       : "4"                 ,
        "CC_MFB_REGION_SIZE"   : "1"                 ,
        "CC_MFB_BLOCK_SIZE"    : "8"                 ,

        "STRADDLING"           : "0"                 ,

        "PCIE_ENDPOINT_MODE"   : 0,
        "PCIE_ENDPOINTS"       : 1,
        "PCIE_CONS"            : 1,
        "PCIE_GEN"             : 4,
        "DMA_PORTS"            : 2,

        "DEVICE"               : "\\\"VERSAL\\\""    ,
        "PCIE_ENDPOINT_TYPE"   : "\\\"VERSAL\\\""    ,
        "__core_params__"      : {"PCIE_TYPE" : "VERSAL"},
    },
    # Versal CPM5 Gen5x8x8: two endpoints with the 1024b AXI interfaces in one PCIe connector
    "versal_gen5x8x8" : {
        "PCIE_ENDPOINT_MODE"   : 1,
        "PCIE_ENDPOINTS"       : 2,
        "PCIE_CONS"            : 1,
        "PCIE_GEN"             : 5,
    },
    "straddling_on" : {
        "STRADDLING"           : "1",
    },
    "endpoints_2_cons_2" : {
        "PCIE_ENDPOINTS"       : 2,
        "PCIE_CONS"            : 2,
    },
    "dma_ports_1" : {
        "DMA_PORTS"            : 1,
    },
    "dma_ports_2" : {
        "DMA_PORTS"            : 2,
    },

    "bar_enable" : {
        "DMA_BAR_ENABLE"       : 1,
    },

    "_combinations_" : {
        "P_TILE_512"               : ("intel_p_tile_512",              ),
        "P_TILE_512_STRADDLING"    : ("intel_p_tile_512", "straddling_on"),
        "P_TILE_256_BIF"           : ("intel_p_tile_256_bif",          ),
        "R_TILE_1024"              : ("intel_r_tile_1024",             ),
        "R_TILE_1024_STRADDLING"   : ("intel_r_tile_1024", "straddling_on"),
        "R_TILE_512_BIF"           : ("intel_r_tile_512_bif",          ),
        "R_TILE_512_BIF_2CONS"     : ("intel_r_tile_512_bif_2cons",    ),
        "USP_512"                  : ("xilinx_usp_512",                ),
        "USP_512_2CONS"            : ("xilinx_usp_512", "endpoints_2_cons_2"),

        "P_TILE_512_CQ"            : ("intel_p_tile_512" , "dma_ports_1", "bar_enable"),
        "P_TILE_512_CQ_STRADDLING" : ("intel_p_tile_512" , "dma_ports_1", "bar_enable", "straddling_on"),
        "R_TILE_1024_CQ"           : ("intel_r_tile_1024", "dma_ports_1", "bar_enable"),
        "USP_512_CQ"               : ("xilinx_usp_512"   , "dma_ports_1", "bar_enable"),

        # Versal: the default run covers 2 DMA ports and the DMA BAR (they cannot be
        # combined) at both widths and both endpoint modes. The commented out
        # combinations are covered by the selected ones; run one of them with
        # -s <its settings>, or uncomment it.
        "VERSAL_512"               : ("xilinx_versal_512",                ),
        # "VERSAL_512_1_PORT"        : ("xilinx_versal_512" , "dma_ports_1"),
        "VERSAL_512_CQ"            : ("xilinx_versal_512" , "dma_ports_1", "bar_enable"),
        "VERSAL_1024"              : ("xilinx_versal_1024",               ),
        # "VERSAL_1024_1_PORT"       : ("xilinx_versal_1024", "dma_ports_1"),
        # "VERSAL_1024_GEN5X8X8"     : ("xilinx_versal_1024", "versal_gen5x8x8", "dma_ports_1"),
        "VERSAL_1024_CQ"           : ("xilinx_versal_1024", "dma_ports_1", "bar_enable"),
        "VERSAL_1024_GEN5X8X8_CQ"  : ("xilinx_versal_1024", "versal_gen5x8x8", "dma_ports_1", "bar_enable"),

    },
}
