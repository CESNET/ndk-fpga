# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "RX_REGIONS"         : "2",
        "TX_REGIONS"         : "1",
        "REGION_SIZE"        : "1",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "32",
        "FRAME_SIZE_MAX"     : "512",
        "FRAME_SIZE_MIN"     : "60",
        "TRANSACTION_COUNT"  : "10000",
    },
    "bus_comb_1" : {
        "RX_REGIONS"         : "1",
        "REGION_SIZE"        : "8",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
    },
    "bus_comb_2" : {
        "RX_REGIONS"         : "2",
        "REGION_SIZE"        : "8",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
    },
    "bus_comb_3" : {
        "RX_REGIONS"         : "1",
        "REGION_SIZE"        : "1",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
    },
    "bus_comb_4" : {
        "RX_REGIONS"         : "1",
        "REGION_SIZE"        : "2",
        "BLOCK_SIZE"         : "4",
        "ITEM_WIDTH"         : "8",
    },
    "bus_comb_5" : {
        "RX_REGIONS"         : "1",
        "REGION_SIZE"        : "2",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
    },
    "bus_comb_6" : {
        "RX_REGIONS"         : "1",
        "REGION_SIZE"        : "4",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
    },
    "bus_comb_7" : {
        "RX_REGIONS"         : "4",
        "REGION_SIZE"        : "8",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
    },
    "tx_regions_same_as_tx" : {
        "RX_REGIONS"         : "2",
        "TX_REGIONS"         : "2",
        "REGION_SIZE"        : "8",
        "BLOCK_SIZE"         : "8",
        "ITEM_WIDTH"         : "8",
    },
    "tx_regions_eq_1" : {
        "TX_REGIONS"         : "1",
    },
    "tx_regions_comb_1" : {
        "TX_REGIONS"         : "2",
    },
    "tx_regions_comb_2" : {
        "TX_REGIONS"         : "4",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    ("bus_comb_1",),
    ("bus_comb_2",),
    ("bus_comb_3",),
    ("bus_comb_4",),
    ("bus_comb_5",),
    ("bus_comb_6",),
    ("bus_comb_7",),

    ("tx_regions_same_as_tx",),

    ("bus_comb_1","tx_regions_eq_1",),
    ("bus_comb_2","tx_regions_eq_1",),
    ("bus_comb_3","tx_regions_eq_1",),
    ("bus_comb_4","tx_regions_eq_1",),
    ("bus_comb_5","tx_regions_eq_1",),
    ("bus_comb_6","tx_regions_eq_1",),
    ("bus_comb_7","tx_regions_eq_1",),

    ("bus_comb_1","tx_regions_comb_1",),
    ("bus_comb_2","tx_regions_comb_1",),
    ("bus_comb_3","tx_regions_comb_1",),
    ("bus_comb_4","tx_regions_comb_1",),
    ("bus_comb_5","tx_regions_comb_1",),
    ("bus_comb_6","tx_regions_comb_1",),
    ("bus_comb_7","tx_regions_comb_1",),

    ("bus_comb_1","tx_regions_comb_2",),
    ("bus_comb_2","tx_regions_comb_2",),
    ("bus_comb_3","tx_regions_comb_2",),
    ("bus_comb_4","tx_regions_comb_2",),
    ("bus_comb_5","tx_regions_comb_2",),
    ("bus_comb_6","tx_regions_comb_2",),
    ("bus_comb_7","tx_regions_comb_2",),
    ),
}
