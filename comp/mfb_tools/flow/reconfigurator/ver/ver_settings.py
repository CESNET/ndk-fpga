# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
#

SETTINGS = {
    "default" : { # The default setting of verification
        "RX_REGIONS"            : "1"                                        ,
        "RX_REGION_SIZE"        : "2"                                        ,
        "RX_BLOCK_SIZE"         : "4"                                        ,
        "RX_ITEM_WIDTH"         : "8"                                        ,
        "TX_REGIONS"            : "8"                                        ,
        "TX_REGION_SIZE"        : "4"                                        ,
        "TX_BLOCK_SIZE"         : "2"                                        ,
        "TX_ITEM_WIDTH"         : "1"                                        ,
        "META_WIDTH"            : "4+32"                                     ,
        "META_MODE"             : "0"                                        ,
        "FIFO_SIZE"             : "16"                                       ,
        "FRAMES_OVER_TX_BLOCK"  : "0"                                        ,
        "FRAMES_OVER_TX_REGION" : "0"                                        ,
        "DEVICE"                : "\\\"ULTRASCALE\\\""                       ,
        "FRAME_SIZE_MIN"        : "1"                                        ,
        "FRAME_SIZE_MAX"        : "4*RX_REGIONS*RX_REGION_SIZE*RX_BLOCK_SIZE",
        "TRANSACTION_COUNT"     : "1000"                                     ,
    },

    "rx_mfb_0" : { #
        "RX_REGIONS"            : "1"                                        ,
        "RX_REGION_SIZE"        : "4"                                        ,
        "RX_BLOCK_SIZE"         : "8"                                        ,
        "RX_ITEM_WIDTH"         : "4"                                        ,
    },
    "rx_mfb_1" : { #
        "RX_REGIONS"            : "4"                                        ,
        "RX_REGION_SIZE"        : "2"                                        ,
        "RX_BLOCK_SIZE"         : "8"                                        ,
        "RX_ITEM_WIDTH"         : "4"                                        ,
    },
    "rx_mfb_2" : { #
        "RX_REGIONS"            : "1"                                        ,
        "RX_REGION_SIZE"        : "4"                                        ,
        "RX_BLOCK_SIZE"         : "8"                                        ,
        "RX_ITEM_WIDTH"         : "8"                                        ,
    },
    "rx_mfb_3" : { #
        "RX_REGIONS"            : "4"                                        ,
        "RX_REGION_SIZE"        : "8"                                        ,
        "RX_BLOCK_SIZE"         : "2"                                        ,
        "RX_ITEM_WIDTH"         : "4"                                        ,
    },
    "rx_mfb_4" : { #
        "RX_REGIONS"            : "4"                                        ,
        "RX_REGION_SIZE"        : "1"                                        ,
        "RX_BLOCK_SIZE"         : "2"                                        ,
        "RX_ITEM_WIDTH"         : "4"                                        ,
    },
    "rx_mfb_5" : { #
        "RX_REGIONS"            : "4"                                        ,
        "RX_REGION_SIZE"        : "4"                                        ,
        "RX_BLOCK_SIZE"         : "1"                                        ,
        "RX_ITEM_WIDTH"         : "4"                                        ,
    },

    "tx_mfb_0" : { #
        "TX_REGIONS"            : "1"                                        ,
        "TX_REGION_SIZE"        : "4"                                        ,
        "TX_BLOCK_SIZE"         : "8"                                        ,
        "TX_ITEM_WIDTH"         : "4"                                        ,
    },
    "tx_mfb_1" : { #
        "TX_REGIONS"            : "4"                                        ,
        "TX_REGION_SIZE"        : "2"                                        ,
        "TX_BLOCK_SIZE"         : "8"                                        ,
        "TX_ITEM_WIDTH"         : "4"                                        ,
    },
    "tx_mfb_2" : { #
        "TX_REGIONS"            : "1"                                        ,
        "TX_REGION_SIZE"        : "4"                                        ,
        "TX_BLOCK_SIZE"         : "8"                                        ,
        "TX_ITEM_WIDTH"         : "8"                                        ,
    },
    "tx_mfb_3" : { #
        "TX_REGIONS"            : "4"                                        ,
        "TX_REGION_SIZE"        : "8"                                        ,
        "TX_BLOCK_SIZE"         : "2"                                        ,
        "TX_ITEM_WIDTH"         : "4"                                        ,
    },
    "tx_mfb_4" : { #
        "TX_REGIONS"            : "4"                                        ,
        "TX_REGION_SIZE"        : "1"                                        ,
        "TX_BLOCK_SIZE"         : "2"                                        ,
        "TX_ITEM_WIDTH"         : "4"                                        ,
    },
    "tx_mfb_5" : { #
        "TX_REGIONS"            : "4"                                        ,
        "TX_REGION_SIZE"        : "4"                                        ,
        "TX_BLOCK_SIZE"         : "1"                                        ,
        "TX_ITEM_WIDTH"         : "4"                                        ,
    },

    "t0" : {
        "RX_REGIONS"            : "1"                                        ,
        "RX_REGION_SIZE"        : "1"                                        ,
        "RX_BLOCK_SIZE"         : "8"                                        ,
        "RX_ITEM_WIDTH"         : "8"                                        ,
        "TX_REGIONS"            : "1"                                        ,
        "TX_REGION_SIZE"        : "8"                                        ,
        "TX_BLOCK_SIZE"         : "8"                                        ,
        "TX_ITEM_WIDTH"         : "8"                                        ,
    },

    "t1" : {
        "RX_REGIONS"            : "1"                                        ,
        "RX_REGION_SIZE"        : "2"                                        ,
        "RX_BLOCK_SIZE"         : "8"                                        ,
        "RX_ITEM_WIDTH"         : "8"                                        ,
        "TX_REGIONS"            : "1"                                        ,
        "TX_REGION_SIZE"        : "8"                                        ,
        "TX_BLOCK_SIZE"         : "8"                                        ,
        "TX_ITEM_WIDTH"         : "8"                                        ,
    },
    "t2" : {
        "RX_REGIONS"            : "1"                                        ,
        "RX_REGION_SIZE"        : "4"                                        ,
        "RX_BLOCK_SIZE"         : "8"                                        ,
        "RX_ITEM_WIDTH"         : "8"                                        ,
        "TX_REGIONS"            : "1"                                        ,
        "TX_REGION_SIZE"        : "8"                                        ,
        "TX_BLOCK_SIZE"         : "8"                                        ,
        "TX_ITEM_WIDTH"         : "8"                                        ,
    },
    "t3" : {
        "RX_REGIONS"            : "1"                                        ,
        "RX_REGION_SIZE"        : "8"                                        ,
        "RX_BLOCK_SIZE"         : "8"                                        ,
        "RX_ITEM_WIDTH"         : "8"                                        ,
        "TX_REGIONS"            : "2"                                        ,
        "TX_REGION_SIZE"        : "8"                                        ,
        "TX_BLOCK_SIZE"         : "8"                                        ,
        "TX_ITEM_WIDTH"         : "8"                                        ,
    },
    "t4" : {
        "RX_REGIONS"            : "2"                                        ,
        "RX_REGION_SIZE"        : "8"                                        ,
        "RX_BLOCK_SIZE"         : "8"                                        ,
        "RX_ITEM_WIDTH"         : "8"                                        ,
        "TX_REGIONS"            : "4"                                        ,
        "TX_REGION_SIZE"        : "8"                                        ,
        "TX_BLOCK_SIZE"         : "8"                                        ,
        "TX_ITEM_WIDTH"         : "8"                                        ,
    },

    "meta_mode_1" : { #
        "META_MODE"             : "1",
    },
    "frames_over_block" : { #
        "FRAMES_OVER_TX_BLOCK"  : "1"                                           ,
        "FRAME_SIZE_MIN"        : "TX_BLOCK_SIZE*TX_ITEM_WIDTH\/RX_ITEM_WIDTH+1",
    },
    "frames_over_region" : { #
        "FRAMES_OVER_TX_BLOCK"  : "1"                                                          ,
        "FRAMES_OVER_TX_REGION" : "1"                                                          ,
        "FRAME_SIZE_MIN"        : "TX_REGION_SIZE*TX_BLOCK_SIZE*TX_ITEM_WIDTH\/RX_ITEM_WIDTH+1",
    },
#    "" : { #
#    },
    "_combinations_" : (
    # Default
    ("default",),

    # No change
    ("rx_mfb_0","tx_mfb_0",                                         "meta_mode_1",),

    # No data shift
    ("rx_mfb_0","tx_mfb_1",                                         "meta_mode_1",),
    ("rx_mfb_2","tx_mfb_1",                                                       ),

    # Data shift without optimalizations
    ("rx_mfb_0","tx_mfb_2",                                                       ),
    ("rx_mfb_3","tx_mfb_0",                                         "meta_mode_1",),
    ("rx_mfb_3","tx_mfb_1",                                                       ),

    # Data shift with optimalizations
    ("rx_mfb_0","tx_mfb_2",                    "frames_over_region","meta_mode_1",),
    ("rx_mfb_3","tx_mfb_0",                    "frames_over_region",              ),
    ("rx_mfb_3","tx_mfb_1","frames_over_block",                     "meta_mode_1",),

    # Configurations with 1
    ("rx_mfb_0","tx_mfb_4",                                         "meta_mode_1",),
    ("rx_mfb_2","tx_mfb_5",                                                       ),
    ("rx_mfb_4","tx_mfb_3",                    "frames_over_region",              ),
    ("rx_mfb_5","tx_mfb_4",                                         "meta_mode_1",),

    # Actually used use-cases
    ("t0","meta_mode_1",),
    ("t1",              ),
    ("t2","meta_mode_1",),
    ("t3","meta_mode_1",),
    ("t4",              ),
    )
}
