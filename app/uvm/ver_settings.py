# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>

#probubly add test chosing
SETTINGS = {
    "default" : { # The default setting of verification
        "ETH_PORTS"            : 2,
        "ETH_STREAMS"          : 2,
        "ETH_CHANNELS"         : 4,
        "ETH_PKT_MTU"          : 2**12,
        "ETH_RX_HDR_WIDTH"     : 102,
        "ETH_TX_HDR_WIDTH"     : 25,
        "PCIE_ENDPOINTS"       : 2,
        "DMA_STREAMS"          : 2,
        "DMA_RX_CHANNELS"      : 8,
        "DMA_TX_CHANNELS"      : 8,
        "DMA_HDR_META_WIDTH"   : 12,
        "DMA_PKT_MTU"          : 2**12,
        "REGIONS"              : 4,
        "MFB_REG_SIZE"         : 8,
        "MFB_BLOCK_SIZE"       : 8,
        "MFB_ITEM_WIDTH"       : 8,
        "MEM_PORTS"            : 1,
        "MEM_ADDR_WIDTH"       : 26,
        "MEM_BURST_WIDTH"      : 7,
        "MEM_DATA_WIDTH"       : 512,
        "MI_DATA_WIDTH"        : 32,
        "MI_ADDR_WIDTH"        : 32,
        "RESET_WIDTH"          : 4,
        "BOARD"                : "\\\"400G1\\\"",
        "DEVICE"               : "\\\"ULTRASCALE\\\"",
        "__core_params__" : {"UVM_TEST" : "test::base"},
    },
    "eth_1" : {
        "ETH_PORTS"            : 1,
        "ETH_STREAMS"          : 1,
        "ETH_CHANNELS"         : 8,
    },
    "dma_1" : {
        "PCIE_ENDPOINTS"       : 1,
        "DMA_STREAMS"          : 1,
        "DMA_RX_CHANNELS"      : 16,
        "DMA_TX_CHANNELS"      : 16,
    },
    "mfb" : {
        "REGIONS"              : 2,
        "MFB_REG_SIZE"         : 8,
        "MFB_BLOCK_SIZE"       : 8,
        "MFB_ITEM_WIDTH"       : 8,
    },

    "mfb_1" : {
        "REGIONS"              : 1,
        "MFB_REG_SIZE"         : 8,
        "MFB_BLOCK_SIZE"       : 8,
        "MFB_ITEM_WIDTH"       : 8,
    },

    "eth_ch1" : {
        "ETH_CHANNELS"         : 1,
    },

    "test_speed" : {
         "__core_params__" : {"UVM_TEST" : "test::full_speed"},
    }
   


    "_combinations_" : (
    ("default",), # Works the same as '("default",),' as the "default" is applied in every combination
    ("default", "test_speed", ), 
    ("eth_1", "dma_1", "mfb",),
    ("dma_1", "eth_ch1", "mfb_1",),
    ("dma_1", "eth_ch1",),
    ("eth_1", "dma_1", "mfb", "test_speed", ),
    ),
}
