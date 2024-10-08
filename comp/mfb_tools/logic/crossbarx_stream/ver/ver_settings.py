# ver_settings.py
# Copyright (C) 2021 CESNET z. s. p. o.
# Author(s): Daniel Kriz   <xkrizd01@vutbr.cz>
#            Daniel Kondys <xkondy00@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "CX_USE_CLK2"           : "0",
        "CX_USE_CLK_ARB"        : "0",

        "OBUF_META_EQ_OUTPUT"   : "1",
        "OBUF_INPUT_EQ_OUTPUT"  : "1",

        "MFB_REGIONS"           : "4",
        "MFB_REGION_SIZE"       : "8",
        "MFB_BLOCK_SIZE"        : "8",
        "MFB_ITEM_WIDTH"        : "8",
        "MFB_META_WIDTH"        : "5",

        "PKT_MTU"               : "2**12",
        "FRAME_SIZE_MAX"        : "PKT_MTU",
        "FRAME_SIZE_MIN"        : "MFB_REGION_SIZE*MFB_BLOCK_SIZE",

        "F_GAP_ADJUST_EN"       : "0" ,
        "F_GAP_ADJUST_SIZE_AVG" : "24",
        "F_GAP_ADJUST_SIZE_MIN" : "24",

        "F_EXTEND_START_EN"     : "0",
        "F_EXTEND_START_SIZE"   : "0",

        "F_EXTEND_END_EN"       : "0",
        "F_EXTEND_END_SIZE"     : "0",

        "SRC_RDY_OFF_CHANCE"    : "0",
        "SRC_RDY_OFF_TIME_MAX"  : "1",
        "SRC_RDY_ON_TIME_MAX"   : "1",

        "DST_RDY_OFF_CHANCE"    : "0",
        "DST_RDY_OFF_TIME_MAX"  : "1",
        "DST_RDY_ON_TIME_MAX"   : "1",

        "DISCARD"               : "1",

        "THROUGHPUT_MEAS_EN"    : "0",

        "RX_CLK_PERIOD"         : "5ns",
        "TX_CLK_PERIOD"         : "5ns",
        "CLK_ARB_PERIOD"        : "5ns",

        "VERBOSE"               : "0",
        "TRANSACTION_COUNT"     : "2000",
        "DEVICE"                : "\\\"STRATIX10\\\"", # STRATIX10, ULTRASCALE, ..
    },
    "clk_setting_1" : { # Clock setting variants
        "TX_CLK_PERIOD"         : "1.8*RX_CLK_PERIOD",
        "CX_USE_CLK2"           : "0",
        "CX_USE_CLK_ARB"        : "0",
        "OBUF_META_EQ_OUTPUT"   : "0",
        "OBUF_INPUT_EQ_OUTPUT"  : "0",
    },
    "clk_setting_2" : {
        "CX_USE_CLK2"           : "1",
        "CX_USE_CLK_ARB"        : "0",
        "OBUF_INPUT_EQ_OUTPUT"  : "0",
    },
    "clk_setting_3" : {
        "CLK_ARB_PERIOD"        : "1.7*RX_CLK_PERIOD",
        "CX_USE_CLK2"           : "0",
        "CX_USE_CLK_ARB"        : "1",
        "OBUF_META_EQ_OUTPUT"   : "1",
        "OBUF_INPUT_EQ_OUTPUT"  : "0",
    },
    "clk_setting_4" : {
        "CLK_ARB_PERIOD"        : "1.7*RX_CLK_PERIOD",
        "CX_USE_CLK2"           : "1",
        "CX_USE_CLK_ARB"        : "0",
        "OBUF_META_EQ_OUTPUT"   : "0",
        "OBUF_INPUT_EQ_OUTPUT"  : "1",
    },
    "clk_setting_5" : {
        "TX_CLK_PERIOD"         : "0.8*RX_CLK_PERIOD",
        "CX_USE_CLK2"           : "1",
        "CX_USE_CLK_ARB"        : "0",
        "OBUF_META_EQ_OUTPUT"   : "0",
        "OBUF_INPUT_EQ_OUTPUT"  : "0",
    },
    "pcie" : { # MFB variants
        "MFB_REGIONS"           : "2",
        "MFB_REGION_SIZE"       : "1",
        "MFB_BLOCK_SIZE"        : "8",
        "MFB_ITEM_WIDTH"        : "32",
    },
    "mfb_setting_1" : {
        "MFB_REGIONS"           : "1",
        "MFB_REGION_SIZE"       : "16",
        "MFB_BLOCK_SIZE"        : "1",
        "MFB_ITEM_WIDTH"        : "16",
    },
    "mfb_setting_2" : {
        "MFB_REGIONS"           : "2",
        "MFB_REGION_SIZE"       : "8",
        "MFB_BLOCK_SIZE"        : "8",
        "MFB_ITEM_WIDTH"        : "8",
    },
    "mfb_setting_3" : {
        "MFB_REGIONS"           : "1",
        "MFB_REGION_SIZE"       : "1",
        "MFB_BLOCK_SIZE"        : "8",
        "MFB_ITEM_WIDTH"        : "8",
    },
    "mfb_setting_4" : {
        "MFB_REGIONS"           : "4",
        "MFB_REGION_SIZE"       : "1",
        "MFB_BLOCK_SIZE"        : "8",
        "MFB_ITEM_WIDTH"        : "32",
    },
    "mfb_setting_5" : {
        "MFB_REGIONS"           : "1",
        "MFB_REGION_SIZE"       : "4",
        "MFB_BLOCK_SIZE"        : "8",
        "MFB_ITEM_WIDTH"        : "8",
    },
    "mfb_meta_var1" : {
        "MFB_META_WIDTH"        : "129",
    },
    "gap_size_var_1" : { # Inter packet gap variants
        "F_GAP_ADJUST_EN"       : "1",
        "F_GAP_ADJUST_SIZE_AVG" : "20",
        "F_GAP_ADJUST_SIZE_MIN" : "17",
    },
    "gap_size_var_2" : { # Do not use with mfb_settings where MFB_REGION_SIZE*MFB_BLOCK_SIZE = 8
        "F_GAP_ADJUST_EN"       : "1",
        "F_GAP_ADJUST_SIZE_AVG" : "63",
        "F_GAP_ADJUST_SIZE_MIN" : "FRAME_SIZE_MIN - MFB_BLOCK_SIZE",
    },
    "extend_start_var_1" : { # Adjust packet size at the front
        "F_EXTEND_START_EN"     : "1",
        "F_EXTEND_START_SIZE"   : "3",
    },
    "extend_start_var_2" : {
        "F_EXTEND_START_EN"     : "1",
        "F_EXTEND_START_SIZE"   : "100",
    },
    "shrink_start_var_1" : {
        "F_EXTEND_START_EN"     : "1",
        "F_EXTEND_START_SIZE"   : "-3",
    },
    "shrink_start_max" : { # Set gap size and end extension accordingly
        "F_EXTEND_START_EN"     : "1",
        "F_EXTEND_START_SIZE"   : "-(FRAME_SIZE_MIN-1)",
    },
    "extend_end_var_1" : { # Adjust packet size at the end
        "F_EXTEND_END_EN"       : "1",
        "F_EXTEND_END_SIZE"     : "5",
    },
    "extend_end_var_2" : {
        "F_EXTEND_END_EN"       : "1",
        "F_EXTEND_END_SIZE"     : "100",
    },
    "shrink_end_var_1" : {
        "F_EXTEND_END_EN"       : "1",
        "F_EXTEND_END_SIZE"     : "-4",
    },
    "shrink_end_max" : { # Set gap size and start extension accordingly
        "F_EXTEND_END_EN"       : "1",
        "F_EXTEND_END_SIZE"     : "-(FRAME_SIZE_MIN-1)",
    },
    "src_and_dst_rdy_var_1" : {
        "SRC_RDY_OFF_CHANCE"    : "50",
        "SRC_RDY_OFF_TIME_MAX"  : "30",
        "SRC_RDY_ON_TIME_MAX"   : "30",
        "DST_RDY_OFF_CHANCE"    : "50",
        "DST_RDY_OFF_TIME_MAX"  : "30",
        "DST_RDY_ON_TIME_MAX"   : "30",
    },
    "src_and_dst_rdy_var_2" : {
        "SRC_RDY_OFF_CHANCE"    : "20",
        "SRC_RDY_OFF_TIME_MAX"  : "10",
        "SRC_RDY_ON_TIME_MAX"   : "10",
        "DST_RDY_OFF_CHANCE"    : "80",
        "DST_RDY_OFF_TIME_MAX"  : "10",
        "DST_RDY_ON_TIME_MAX"   : "10",
    },
    "disable_discard" : { # Discard
        "DISCARD"               : "0",
    },
    "always_discard" : {
        "DISCARD"               : "2",
    },
    "speed_measure_en" : {
        "THROUGHPUT_MEAS_EN"    : "1",
    },
    "verbose" : {
        "VERBOSE"               : "1",
    },
    "_combinations_" : (
    (), # Works the same as '("default",),' as the "default" is applied in every combination
    # Clock         , MFB            , Metadata       , Gap             , Adjust size start   , Adjust size end   , SRC and DST ready      , Discard
    ("clk_setting_1", "pcie"         ,                                    "extend_start_var_1",                     "src_and_dst_rdy_var_1",                   ),
    ("clk_setting_2", "mfb_setting_1", "mfb_meta_var1", "gap_size_var_1", "shrink_start_var_1",                                                                ),
    ("clk_setting_4", "mfb_setting_2", "mfb_meta_var1",                                         "extend_end_var_1", "src_and_dst_rdy_var_1",                   ),
    (                 "mfb_setting_3",                  "gap_size_var_1",                       "shrink_end_var_1", "src_and_dst_rdy_var_2",                   ),
    ("clk_setting_3", "mfb_setting_4",                                    "extend_start_var_1", "extend_end_var_1",                                            ),
    ("clk_setting_2", "mfb_setting_5",                                    "extend_start_var_1", "shrink_end_var_1",                                            ),
    ("clk_setting_5", "pcie"         , "mfb_meta_var1", "gap_size_var_1", "shrink_start_var_1", "shrink_end_var_1", "src_and_dst_rdy_var_1",                   ),
    ("clk_setting_1", "mfb_setting_1",                  "gap_size_var_2", "shrink_start_var_1", "extend_end_var_1", "src_and_dst_rdy_var_1",                   ),
    (                 "mfb_setting_2",                  "gap_size_var_1",                                           "src_and_dst_rdy_var_2", "disable_discard",),
    (                 "mfb_setting_3", "mfb_meta_var1", "gap_size_var_1", "extend_start_var_2", "extend_end_var_2",                          "always_discard" ,),
    ("clk_setting_5", "mfb_setting_4", "mfb_meta_var1",                   "shrink_start_var_1", "shrink_end_var_1",                          "always_discard" ,),
    ("clk_setting_4", "mfb_setting_5",                  "gap_size_var_2", "extend_start_var_2", "shrink_end_max"  , "src_and_dst_rdy_var_2",                   ),
    ("clk_setting_3", "pcie"         , "mfb_meta_var1", "gap_size_var_1", "shrink_start_max"  , "extend_end_var_2", "src_and_dst_rdy_var_1",                   ),
    (                 "mfb_setting_1", "mfb_meta_var1", "gap_size_var_2",                       "shrink_end_max"  ,                          "disable_discard",),
    ("clk_setting_1", "mfb_setting_2",                  "gap_size_var_2", "shrink_start_max",                                                "disable_discard",),
    ("clk_setting_4", "mfb_setting_3",                  "gap_size_var_1",                                                                    "always_discard" ,),
    ("clk_setting_2", "mfb_setting_4", "mfb_meta_var1",                   "shrink_start_var_1", "extend_end_var_2", "src_and_dst_rdy_var_1",                   ),
    ("clk_setting_5", "mfb_setting_5", "mfb_meta_var1", "gap_size_var_1", "extend_start_var_2", "shrink_end_var_1", "src_and_dst_rdy_var_2",                   ),
    ("clk_setting_5", "pcie"         ,                                    "extend_start_var_2", "extend_end_var_2", "src_and_dst_rdy_var_1", "disable_discard",),
    (                 "mfb_setting_1", "mfb_meta_var1", "gap_size_var_1", "shrink_start_var_1", "shrink_end_var_1", "src_and_dst_rdy_var_2", "disable_discard",),
    ("clk_setting_2", "mfb_setting_2",                  "gap_size_var_2", "extend_start_var_2", "shrink_end_max"  ,                          "always_discard" ,),
    (                 "mfb_setting_3", "mfb_meta_var1",                   "shrink_start_max"  , "extend_end_var_2",                          "always_discard" ,),
    ("clk_setting_2", "mfb_setting_4", "mfb_meta_var1", "gap_size_var_1",                       "shrink_end_max"  , "src_and_dst_rdy_var_1", "disable_discard",),
    ("clk_setting_1", "mfb_setting_5",                  "gap_size_var_2", "shrink_start_max"  ,                                              "disable_discard",),
    ("clk_setting_4", "mfb_setting_1",                                                                                                       "always_discard" ,),
    (                 "mfb_setting_2",                  "gap_size_var_1", "shrink_start_var_1", "extend_end_var_2", "src_and_dst_rdy_var_1", "disable_discard",),
    ("clk_setting_3", "pcie"         , "mfb_meta_var1", "gap_size_var_1", "extend_start_var_2", "shrink_end_var_1", "src_and_dst_rdy_var_2", "disable_discard",),
    ),
}
