# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "TX_REGIONS"        : "4",
        "TX_REGION_SIZE"    : "8",
        "TX_BLOCK_SIZE"     : "8",
        "TX_ITEM_WIDTH"     : "8",
        "RX_REGIONS"        : "TX_REGIONS",
        "RX_REGION_SIZE"    : "TX_REGION_SIZE",
        "RX_BLOCK_SIZE"     : "TX_BLOCK_SIZE",
        "RX_ITEM_WIDTH"     : "TX_ITEM_WIDTH",
        "RX_INCLUDE_CRC"    : "0",
        "RX_INCLUDE_IPG"    : "0",
        "CRC_INSERT_EN"     : "1",
        "IPG_GENERATE_EN"   : "1",
        "FRAME_SIZE_MAX"    : "512",
        "FRAME_SIZE_MIN"    : "50",
        "TRANSACTION_COUNT" : "2500",
        "RX_CLK_PERIOD"     : "5ns",
        "TX_CLK_PERIOD"     : "4ns",
        "MI_CLK_PERIOD"     : "7ns",
    },
    "tx1024b" : {
        "TX_REGIONS"        : "2",
    },
    "tx512b" : {
        "TX_REGIONS"        : "1",
    },
    "tx256b" : {
        "TX_REGIONS"        : "1",
        "TX_REGION_SIZE"    : "4",
    },
    "tx64b" : {
        "TX_REGIONS"        : "1",
        "TX_REGION_SIZE"    : "1",
    },
    "tx64b4blk" : {
        "TX_REGIONS"        : "1",
        "TX_REGION_SIZE"    : "2",
        "TX_BLOCK_SIZE"     : "4",
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
        "CRC_INSERT_EN"     : "0",
    },
    "hard_ip_rdy" : {
        "RX_INCLUDE_CRC"    : "0",
        "RX_INCLUDE_IPG"    : "0",
        "CRC_INSERT_EN"     : "0",
        "IPG_GENERATE_EN"   : "0",
    },
    "hard_ip_rdy_crc" : {
        "RX_INCLUDE_CRC"    : "0",
        "RX_INCLUDE_IPG"    : "1",
        "CRC_INSERT_EN"     : "1",
        "IPG_GENERATE_EN"   : "0",
    },
    "tx_slow" : {
        "RX_CLK_PERIOD"     : "5ns",
        "TX_CLK_PERIOD"     : "8ns",
    },

    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("tx1024b",),
    ("tx512b",),
    ("tx512b","hard_ip_rdy",),
    ("tx512b","hard_ip_rdy","rx_include_crc","frames_small",),
    ("tx256b","tx_slow","frames_big",),
    ("tx256b","rx512b","hard_ip_rdy",),
    #("tx64b",),
    #("tx64b","tx_slow",),
    #("tx64b4blk","rx64b",),
    #("tx64b4blk","rx512b","frames_small",),
    ),
}
