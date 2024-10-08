# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "MII_DATA_WIDTH"    : "2048",
        "MII_LANE_WIDTH"    : "64",
        "RX_REGIONS"        : "RXA_REGIONS",
        "RX_REGION_SIZE"    : "RXA_REGION_SIZE",
        "RX_BLOCK_SIZE"     : "RXA_BLOCK_SIZE",
        "RX_ITEM_WIDTH"     : "RXA_ITEM_WIDTH",
        "RX_INCLUDE_CRC"    : "0",
        "RX_INCLUDE_IPG"    : "0",
        "FRAME_SIZE_MAX"    : "512",
        "FRAME_SIZE_MIN"    : "50",
        "TRANSACTION_COUNT" : "2500",
        "RX_CLK_PERIOD"     : "5ns",
        "TX_CLK_PERIOD"     : "4ns",
        "MI_CLK_PERIOD"     : "7ns",
    },
    "tx1024b" : {
        "MII_DATA_WIDTH"    : "1024",
    },
    "tx512b" : {
        "MII_DATA_WIDTH"    : "512",
    },
    "tx256b" : {
        "MII_DATA_WIDTH"    : "256",
    },
    "tx64b" : {
        "MII_DATA_WIDTH"    : "64",
    },
    "tx64b4blk" : {
        "MII_DATA_WIDTH"    : "64",
        "MII_LANE_WIDTH"    : "32",
    },
    "rx512b" : {
        "RX_REGIONS"        : "1",
        "RX_REGION_SIZE"    : "8",
        "RX_BLOCK_SIZE"     : "8",
        "RX_ITEM_WIDTH"     : "8",
    },
    "rx64b" : {
        "RX_REGIONS"        : "1",
        "RX_REGION_SIZE"    : "1",
        "RX_BLOCK_SIZE"     : "8",
        "RX_ITEM_WIDTH"     : "8",
    },
    "frames_big" : {
        "FRAME_SIZE_MAX"    : "4096",
        "FRAME_SIZE_MIN"    : "256",
    },
    "frames_small" : {
        "FRAME_SIZE_MAX"    : "128",
        "FRAME_SIZE_MIN"    : "50",
    },
    "rx_include_crc" : {
        "RX_INCLUDE_CRC"    : "1",
    },
    "tx_slow" : {
        "RX_CLK_PERIOD"     : "5ns",
        "TX_CLK_PERIOD"     : "8ns",
    },

    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("tx1024b",),
    ("tx512b",),
    ("tx512b","frames_small",),
    ("tx512b","rx_include_crc",),
    ("tx256b","tx_slow","frames_big",),
    ("tx256b","rx512b",),
    #("tx64b",),
    #("tx64b","tx_slow",),
    #("tx64b4blk","rx64b",),
    #("tx64b4blk","rx512b","frames_small",),
    ),
}
