# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
#

SETTINGS = {
    "default" : { # The default setting of verification
        "REGIONS"          : "2"                                     ,
        "RX_REGION_SIZE"   : "1"                                     ,
        "TX_REGION_SIZE"   : "1"                                     ,
        "RX_BLOCK_SIZE"    : "8"                                     ,
        "ITEM_WIDTH"       : "4"                                     ,
        "META_WIDTH"       : "4"                                     ,
        "META_MODE"        : "0"                                     ,
        "FIFO_SIZE"        : "16"                                    ,
        "FRAME_ALIGN"      : "0"                                     ,
        "DEVICE"           : "\\\"ULTRASCALE\\\""                    ,
        "FRAME_SIZE_MIN"   : "1"                                     ,
        "FRAME_SIZE_MAX"   : "8*REGIONS*RX_REGION_SIZE*RX_BLOCK_SIZE",
        "TRANSACTION_COUNT": "1000"                                  ,
    },
    "2_rx_blocks" : { #
        "RX_REGION_SIZE"   : "2"                                  ,
    },
    "2_tx_blocks" : { #
        "TX_REGION_SIZE"   : "2"                                  ,
    },
    "8_rx_blocks" : { #
        "RX_REGION_SIZE"   : "8"                                  ,
    },
    "8_tx_blocks" : { #
        "TX_REGION_SIZE"   : "8"                                  ,
    },
    "meta_mode_1" : { #
        "META_MODE"        : "1"                                  ,
    },
    "frame_align_1" : { #
        "FRAME_ALIGN"      : "1"                                            ,
        "FRAME_SIZE_MIN"   : "RX_BLOCK_SIZE*RX_REGION_SIZE\\\/TX_REGION_SIZE+1",
    },
#    "" : { #
#    },
    "_combinations_" : (
    ("default",),
    ("2_rx_blocks",),
    ("2_tx_blocks",),
    ("8_rx_blocks",),
    ("8_tx_blocks",),
    ("2_rx_blocks","8_tx_blocks",),
    ("8_rx_blocks","2_tx_blocks",),
    ("8_rx_blocks","2_tx_blocks","meta_mode_1"),
    ("8_rx_blocks","2_tx_blocks","frame_align_1"),
    )
}
