# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>
#            Jakub Cabal <cabal@cesnet.cz>

SETTINGS = {
    "default" : { # The default setting of verification (MERGER_INPUTS=2)
        "MERGER_INPUTS"   : "2",
        "MFB_REGIONS"     : "1",
        "MFB_REGION_SIZE" : "4",
        "MFB_BLOCK_SIZE"  : "8",
        "MFB_ITEM_WIDTH"  : "8",
        "MFB_META_WIDTH"  : "8",
        "CNT_MAX"         : "64",

        "FRAME_SIZE_MAX"    : "512",
        "FRAME_SIZE_MIN"    : "60",
        "TRANSACTION_COUNT" : "10000",

        "int unsigned RX_MFB_SRC_RDY_FALL_CHANCE  \\[\\]" : "{30,20}",
        "int unsigned RX_MFB_SRC_RDY_FALL_TIME_MAX\\[\\]" : "{20,10}",

        "TX_MFB_DST_RDY_FALL_CHANCE"   : "10",
        "TX_MFB_DST_RDY_FALL_TIME_MAX" : "10",
    },

    # ---- Input count sweeps (each carries matching-length RX arrays) ----
    "inputs_1" : {
        "MERGER_INPUTS"                                   : "1",
        "int unsigned RX_MFB_SRC_RDY_FALL_CHANCE  \\[\\]" : "{33}",
        "int unsigned RX_MFB_SRC_RDY_FALL_TIME_MAX\\[\\]" : "{20}",
    },
    "inputs_2" : {
        "MERGER_INPUTS"                                   : "2",
        "int unsigned RX_MFB_SRC_RDY_FALL_CHANCE  \\[\\]" : "{33,44}",
        "int unsigned RX_MFB_SRC_RDY_FALL_TIME_MAX\\[\\]" : "{20,20}",
    },
    "inputs_3" : {
        "MERGER_INPUTS"                                   : "3",
        "int unsigned RX_MFB_SRC_RDY_FALL_CHANCE  \\[\\]" : "{33,80,20}",
        "int unsigned RX_MFB_SRC_RDY_FALL_TIME_MAX\\[\\]" : "{20,20,10}",
    },
    "inputs_4" : {
        "MERGER_INPUTS"                                   : "4",
        "int unsigned RX_MFB_SRC_RDY_FALL_CHANCE  \\[\\]" : "{33,50,80,20}",
        "int unsigned RX_MFB_SRC_RDY_FALL_TIME_MAX\\[\\]" : "{20,10,20,10}",
    },

    # ---- CNT_MAX (starvation / switching threshold) sweeps ----
    "cnt_small" : {
        "CNT_MAX" : "4",
    },
    "cnt_large" : {
        "CNT_MAX" : "256",
    },

    # ---- MFB dimension combos (reused from the original merger_simple sweep) ----
    "pcie" : {
        "MFB_REGIONS"     : "2",
        "MFB_REGION_SIZE" : "1",
        "MFB_BLOCK_SIZE"  : "8",
        "MFB_ITEM_WIDTH"  : "32",
    },
    "region_comb_1" : {
        "MFB_REGIONS"     : "1",
        "MFB_REGION_SIZE" : "8",
        "MFB_BLOCK_SIZE"  : "8",
        "MFB_ITEM_WIDTH"  : "8",
    },
    "region_comb_2" : {
        "MFB_REGIONS"     : "2",
        "MFB_REGION_SIZE" : "8",
        "MFB_BLOCK_SIZE"  : "8",
        "MFB_ITEM_WIDTH"  : "8",
    },
    "region_comb_3" : {
        "MFB_REGIONS"     : "1",
        "MFB_REGION_SIZE" : "1",
        "MFB_BLOCK_SIZE"  : "8",
        "MFB_ITEM_WIDTH"  : "8",
    },
    "region_comb_4" : {
        "MFB_REGIONS"     : "1",
        "MFB_REGION_SIZE" : "2",
        "MFB_BLOCK_SIZE"  : "4",
        "MFB_ITEM_WIDTH"  : "8",
    },
    "region_comb_5" : {
        "MFB_REGIONS"     : "1",
        "MFB_REGION_SIZE" : "2",
        "MFB_BLOCK_SIZE"  : "8",
        "MFB_ITEM_WIDTH"  : "8",
    },
    "region_comb_6" : {
        "MFB_REGIONS"     : "4",
        "MFB_REGION_SIZE" : "8",
        "MFB_BLOCK_SIZE"  : "8",
        "MFB_ITEM_WIDTH"  : "8",
    },

    # ---- TX backpressure variant ----
    "slow_tx" : {
        "TX_MFB_DST_RDY_FALL_CHANCE"   : "60",
        "TX_MFB_DST_RDY_FALL_TIME_MAX" : "20",
    },

    "_combinations_" : (
    (), # Works the same as '("default",)' as the "default" is applied in every combination
    ("inputs_2",),
    ("inputs_3",),
    ("inputs_4",),
    ("inputs_1",),
    ("inputs_2", "cnt_small"),
    ("inputs_3", "cnt_small"),
    ("inputs_3", "cnt_large"),
    ("inputs_4", "cnt_large"),
    ("region_comb_1",),
    ("region_comb_2",),
    ("region_comb_3",),
    ("region_comb_4",),
    ("region_comb_5",),
    ("region_comb_6",),
    ("pcie",),
    ("inputs_3", "slow_tx"),
    ("inputs_4", "region_comb_1", "cnt_small"),
    ("inputs_2", "pcie", "slow_tx"),
    ),

    # Only run a random subset of the combinations to keep CI time reasonable.
    "_combinations_run_percentage_" : 30,
}
