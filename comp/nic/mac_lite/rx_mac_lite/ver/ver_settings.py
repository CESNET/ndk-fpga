# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Jakub Cabal <cabal@cesnet.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "RX_REGIONS"        : "4",
        "RX_REGION_SIZE"    : "8",
        "RX_BLOCK_SIZE"     : "8",
        "RX_ITEM_WIDTH"     : "8",
        "TX_REGIONS"        : "RX_REGIONS",
        "TX_REGION_SIZE"    : "RX_REGION_SIZE",
        "TX_BLOCK_SIZE"     : "RX_BLOCK_SIZE",
        "TX_ITEM_WIDTH"     : "RX_ITEM_WIDTH",
        "RESIZE_BUFFER"     : "0",
        "CRC_CHECK_EN"      : "1",
        "MAC_CHECK_EN"      : "1",
        "CRC_IS_RECEIVED"   : "1",
        "CRC_REMOVE_EN"     : "1",
        "FRAME_SIZE_MAX"    : "512",
        "FRAME_SIZE_MIN"    : "50",
        "TRANSACTION_COUNT" : "2500",
        "RX_CLK_PERIOD"     : "5.1ns",
        "TX_CLK_PERIOD"     : "5ns",
        "MI_CLK_PERIOD"     : "7ns",
    },
    "resbuf" : {
        "RESIZE_BUFFER"     : "1",
    },
    "rx1024b" : {
        "RX_REGIONS"        : "2",
    },
    "rx512b" : {
        "RX_REGIONS"        : "1",
    },
    "rx256b" : {
        "RX_REGIONS"        : "1",
        "RX_REGION_SIZE"    : "4",
    },
    "rx64b" : {
        "RX_REGIONS"        : "1",
        "RX_REGION_SIZE"    : "1",
    },
    "tx512b" : {
        "TX_REGIONS"        : "1",
        "TX_REGION_SIZE"    : "8",
        "TX_BLOCK_SIZE"     : "8",
        "TX_ITEM_WIDTH"     : "8",
    },
    "tx64b" : {
        "TX_REGIONS"        : "1",
        "TX_REGION_SIZE"    : "1",
        "TX_BLOCK_SIZE"     : "8",
        "TX_ITEM_WIDTH"     : "8",
    },
    "frames_big" : {
        "FRAME_SIZE_MAX"    : "4096",
        "FRAME_SIZE_MIN"    : "256",
        "TRANSACTION_COUNT" : "1500",
    },
    "frames_small" : {
        "FRAME_SIZE_MAX"    : "128",
        "FRAME_SIZE_MIN"    : "50",
    },
    "mac_check_disable" : {
        "MAC_CHECK_EN"      : "0",
    },
    "hard_ip_rdy" : {
        "CRC_CHECK_EN"      : "0",
        "CRC_IS_RECEIVED"   : "0",
        "CRC_REMOVE_EN"     : "0",
    },
    "tx_slow" : {
        "RX_CLK_PERIOD"     : "5ns",
        "TX_CLK_PERIOD"     : "8ns",
    },
    "400g_ftile" : {
        "RX_REGIONS"        : "2",
        "RX_REGION_SIZE"    : "8",
        "RX_BLOCK_SIZE"     : "8",
        "RX_ITEM_WIDTH"     : "8",
        "TX_REGIONS"        : "4",
        "TX_REGION_SIZE"    : "RX_REGION_SIZE",
        "TX_BLOCK_SIZE"     : "RX_BLOCK_SIZE",
        "TX_ITEM_WIDTH"     : "RX_ITEM_WIDTH",
        "RESIZE_BUFFER"     : "1",
        "CRC_CHECK_EN"      : "0",
        "MAC_CHECK_EN"      : "1",
        "CRC_IS_RECEIVED"   : "0",
        "CRC_REMOVE_EN"     : "0",
        "FRAME_SIZE_MAX"    : "100",
        "FRAME_SIZE_MIN"    : "100",
        "TRANSACTION_COUNT" : "5000",
        "RX_CLK_PERIOD"     : "2.4ns",
        "TX_CLK_PERIOD"     : "5ns",
        "MI_CLK_PERIOD"     : "10ns",
    },

    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("rx1024b",),
    ("rx512b","mac_check_disable",),
    ("rx512b","frames_big","mac_check_disable",),
    ("rx512b","hard_ip_rdy",),
    ("rx512b","hard_ip_rdy","frames_small",),
    ("rx256b","frames_small",),
    ("rx256b","tx512b","mac_check_disable",),
    ("rx64b","frames_big",),
    ("rx64b","tx512b","tx_slow","resbuf",),
    ("400g_ftile",),
    ),
}
