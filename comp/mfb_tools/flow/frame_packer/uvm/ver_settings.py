# ver_settings.py
# Copyright (C) 2024 CESNET z. s. p. o.
# Author(s): David Beneš <xbenes52@vutbr.cz>

# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    "default" : { # The default setting of verification
        "MFB_REGIONS"        : "4",
        "MFB_REGION_SIZE"    : "8",
        "MFB_BLOCK_SIZE"     : "8",
        "MFB_ITEM_WIDTH"     : "8",

        "RX_CHANNELS"        : "16",

        "FRAME_SIZE_MIN"     : "64",
        "FRAME_SIZE_MAX"     : "2**14 - 1",

        "SPKT_SIZE_MIN"      : "2**13",
        "TIMEOUT_CLK_NO"     : "2**12",

        "SEQ_MIN"            : "5",
        "SEQ_MAX"            : "8",
        "RX_GAP_PROBABILITY" : "30",
        "MVB_TX_STALL_CLKS"  : "0",
    },
    "one_region" : {
        "MFB_REGIONS"        : "1",
    },
    "four_regions" : {
        "MFB_REGIONS"        : "4",
    },
    "two_channels" : {
        "RX_CHANNELS"        : "2",
    },
    "thirty-two_channels" : {
        "RX_CHANNELS"        : "32",
    },
    "small_frames" : {
        "FRAME_SIZE_MIN"     : "64",
        "FRAME_SIZE_MAX"     : "128",
    },
    # Big packets are expensive to simulate - less traffic and no RX gaps
    "big_frames" : {
        "FRAME_SIZE_MIN"            : "2**13",
        "FRAME_SIZE_MAX"            : "2**14",
        "SEQ_MIN"                   : "1",
        "SEQ_MAX"                   : "2",
        "RX_GAP_PROBABILITY"        : "0",
    },
    "short_timeout" : {
        "TIMEOUT_CLK_NO"     : "2**9",
    },
    "small_spkts" : {
        "SPKT_SIZE_MIN"     : "2**10",
    },
    # SuperPacket limit smaller than one MFB word - a timeout word can reach the limit on its own
    "tiny_spkts" : {
        "SPKT_SIZE_MIN"     : "2**7",
    },
    # Long TX MVB stall with many small SuperPackets - more MVB items than the DUT MVB FIFO can store
    "mvb_stall" : {
        "SPKT_SIZE_MIN"      : "2**9",
        "MVB_TX_STALL_CLKS"  : "40000",
        "SEQ_MIN"            : "40",
        "SEQ_MAX"            : "50",
        "RX_GAP_PROBABILITY" : "0",
    },

    "_combinations_" : (
    (                                                          ), # Default
    ("one_region",                                             ),
    ("two_channels",                                           ),
    ("one_region",          "short_timeout",                   ),
    ("four_regions",        "short_timeout",                   ),
    ("tiny_spkts",          "small_frames",   "short_timeout", ),
    (                       "small_spkts",                     ),
    ("mvb_stall",           "small_frames",                    ),
    (                       "big_frames",                      ),
    ("thirty-two_channels", "small_frames",                    ),
    ),
}
