# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
#

SETTINGS = {
    "default" : { # The default setting of verification
        "REGIONS"          : "2"                                  ,
        "REGION_SIZE"      : "2"                                  ,
        "RX_BLOCK_SIZE"    : "1"                                  ,
        "TX_BLOCK_SIZE"    : "1"                                  ,
        "RX_ITEM_WIDTH"    : "8"                                  ,
        "META_WIDTH"       : "4+32"                               ,
        "META_MODE"        : "0"                                  ,
        "FIFO_SIZE"        : "16"                                 ,
        "FRAME_ALIGN"      : "0"                                  ,
        "DEVICE"           : "\\\"ULTRASCALE\\\""                 ,
        "FRAME_SIZE_MIN"   : "1"                                  ,
        "FRAME_SIZE_MAX"   : "8*REGIONS*REGION_SIZE*RX_BLOCK_SIZE",
        "TRANSACTION_COUNT": "1000"                               ,
    },
    "2_rx_items" : { #
        "RX_BLOCK_SIZE"   : "2"                                   ,
    },
    "2_tx_items" : { #
        "TX_BLOCK_SIZE"   : "2"                                   ,
    },
    "8_rx_items" : { #
        "RX_BLOCK_SIZE"   : "8"                                   ,
    },
    "8_tx_items" : { #
        "TX_BLOCK_SIZE"   : "8"                                   ,
    },
    "meta_mode_1" : { #
        "META_MODE"        : "1"                                  ,
    },
#    "" : { #
#    },
    "_combinations_" : (
    ("default",),
    ("2_rx_items",),
    ("2_tx_items",),
    ("8_rx_items",),
    ("8_tx_items",),
    ("2_rx_items","8_tx_items",),
    ("8_rx_items","2_tx_items",),
    ("8_rx_items","2_tx_items","meta_mode_1"),
    )
}
