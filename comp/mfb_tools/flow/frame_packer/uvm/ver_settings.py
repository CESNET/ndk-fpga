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
    "sixteen_channels" : {
        "RX_CHANNELS"        : "16",
    },
    "thirty-two_channels" : {
        "RX_CHANNELS"        : "32",
    },
    "small_frames" : {
        "FRAME_SIZE_MIN"     : "64",
        "FRAME_SIZE_MAX"     : "128",
    },
    "big_frames" : {
        "FRAME_SIZE_MIN"     : "2**13",
        "FRAME_SIZE_MAX"     : "2**14 - 1",
    },
    "short_timeout" : {
        "TIMEOUT_CLK_NO"     : "2**9",
    },
    "long_timeout" : {
        "TIMEOUT_CLK_NO"     : "2**12",
    },
    "small_spkts" : {
        "SPKT_SIZE_MIN"     : "2**10",
    },
    "big_spkts" : {
        "SPKT_SIZE_MIN"     : "2**13",
    },

    "_combinations_" : (
    (                                         ), # Default
    ("one_region",                            ),
    ("two_channels",                          ),
    ("sixteen_channels",                      ),
    ("four_regions",        "short_timeout"  ,),
    (                       "long_timeout"   ,),
    (                       "small_spkts"    ,),
    (                       "big_spkts"      ,),
    (                       "big_frames"     ,),
    ("thirty-two_channels", "small_frames"   ,),
    ),
}
