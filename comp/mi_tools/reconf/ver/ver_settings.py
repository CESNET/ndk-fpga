# ver_settings.py
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Jan Kubalek <kubalek@cesnet.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    "default" : { # The default setting of verification
        "TRANSACTION_COUNT" : "20000" ,
        "RX_DATA_WIDTH"     : "32"    ,
        "TX_DATA_WIDTH"     : "32"    ,
        "ADDR_WIDTH"        : "32"    ,
        "META_WIDTH"        : "16"    ,
        "VERBOSITY"         : "0"     ,
    },

    "verbose" : {
        "VERBOSITY"         : "3"     ,
    },

    "rx_data_8" : {
        "RX_DATA_WIDTH"     : "8"     ,
    },
    "rx_data_16" : {
        "RX_DATA_WIDTH"     : "16"    ,
    },

    "tx_data_8" : {
        "TX_DATA_WIDTH"     : "8"     ,
    },
    "tx_data_16" : {
        "TX_DATA_WIDTH"     : "16"    ,
    },

    "addr_5" : {
        "ADDR_WIDTH"        : "5"     ,
    },
    "addr_55" : {
        "ADDR_WIDTH"        : "55"    ,
    },

    "meta_1" : {
        "META_WIDTH"        : "1"     ,
    },
    "meta_55" : {
        "META_WIDTH"        : "55"    ,
    },

    "_combinations_" : (
    ("default",),

    ("rx_data_8" ,"tx_data_8" ,"addr_55","meta_55",),
    (             "tx_data_16","addr_5" ,          ),
    (                          "addr_55","meta_55",),
    (             "tx_data_8" ,          "meta_1" ,),
    ("rx_data_16","tx_data_8" ,"addr_5" ,"meta_1" ,),
    ("rx_data_8" ,             "addr_55",          ),
    ("rx_data_8" ,"tx_data_8" ,                    ),
    ("rx_data_16","tx_data_16",                    ),
    (             "tx_data_8" ,          "meta_55",),
    (                          "addr_5" ,"meta_1" ,),
    ("rx_data_16",             "addr_55",          ),
    ("rx_data_8" ,"tx_data_16","addr_5" ,          ),
    )
}
