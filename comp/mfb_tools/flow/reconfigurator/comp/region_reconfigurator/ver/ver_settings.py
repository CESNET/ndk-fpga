# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
#

SETTINGS = {
    "default" : { # The default setting of verification
        "RX_REGIONS"       : "1"                                     ,
        "TX_REGIONS"       : "1"                                     ,
        "RX_REGION_SIZE"   : "8"                                     ,
        "BLOCK_SIZE"       : "2"                                     ,
        "ITEM_WIDTH"       : "4"                                     ,
        "META_WIDTH"       : "4"                                     ,
        "META_MODE"        : "0"                                     ,
        "FIFO_SIZE"        : "16"                                    ,
        "DEVICE"           : "\\\"ULTRASCALE\\\""                    ,
        "FRAME_SIZE_MIN"   : "1"                                     ,
        "FRAME_SIZE_MAX"   : "8*RX_REGIONS*RX_REGION_SIZE*BLOCK_SIZE",
        "TRANSACTION_COUNT": "1000"                                  ,
    },
    "2_rx_regs" : { #
        "RX_REGIONS"       : "2"                                  ,
    },
    "2_tx_regs" : { #
        "TX_REGIONS"       : "2"                                  ,
    },
    "8_rx_regs" : { #
        "RX_REGIONS"       : "8"                                  ,
    },
    "8_tx_regs" : { #
        "TX_REGIONS"       : "8"                                  ,
    },
    "meta_mode_1" : { #
        "META_MODE"        : "1"                                  ,
    },
#    "" : { #
#    },
    "_combinations_" : (
    ("default",),
    ("2_rx_regs",),
    ("2_tx_regs",),
    ("8_rx_regs",),
    ("8_tx_regs",),
    ("2_rx_regs","8_tx_regs",),
    ("8_rx_regs","2_tx_regs",),
    ("8_rx_regs","2_tx_regs","meta_mode_1"),
    )
}
