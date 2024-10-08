# ver_settings.py
# Copyright (C) 2020 CESNET z. s. p. o.
# Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

SETTINGS = {
    "default" : { # The default setting of verification
        "MERGER_INPUTS"                                        : "2"                                          ,

        "MVB_ITEMS"                                            : "2"                                          ,
        "MVB_ITEM_WIDTH"                                       : "16"                                         ,

        "MFB_REGIONS"                                          : "2"                                          ,
        "MFB_REG_SIZE"                                         : "1"                                          ,
        "MFB_BLOCK_SIZE"                                       : "4"                                          ,
        "MFB_ITEM_WIDTH"                                       : "4"                                          ,
        "MFB_META_WIDTH"                                       : "1"                                          ,

        "INPUT_FIFO_SIZE"                                      : "8"                                          ,
        "bool RX_PAYLOAD_EN\\[MERGER_INPUTS-1:0\\]"            : "{TRUE, TRUE}"                               ,
        "IN_PIPE_EN"                                           : "FALSE"                                      ,
        "OUT_PIPE_EN"                                          : "FALSE"                                      ,
        "DEVICE"                                               : "\\\"ULTRASCALE\\\""                         ,

        "FRAME_SIZE_MAX"                                       : "MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*3"  ,
        "FRAME_SIZE_MIN"                                       : "1"                                          ,
        "TRANSACTION_COUNT"                                    : "10000"                                      ,

        "int unsigned RX_MVB_SRC_RDY_FALL_CHANCE  \\[\\]"      : "{10,20}"                                    ,
        "int unsigned RX_MVB_SRC_RDY_FALL_TIME_MAX\\[\\]"      : "{10,20}"                                    ,
        "int unsigned RX_MFB_SRC_RDY_FALL_CHANCE  \\[\\]"      : "{30,20}"                                    ,
        "int unsigned RX_MFB_SRC_RDY_FALL_TIME_MAX\\[\\]"      : "{20,10}"                                    ,

        "TX_MVB_DST_RDY_FALL_CHANCE"                           : "20"                                         ,
        "TX_MVB_DST_RDY_FALL_TIME_MAX"                         : "20"                                         ,
        "TX_MFB_DST_RDY_FALL_CHANCE"                           : "10"                                         ,
        "TX_MFB_DST_RDY_FALL_TIME_MAX"                         : "10"                                         ,

        "FULL_PRINT"                                           : "FALSE"                                      ,
    },

    "inputs_1_0" : {
        "MERGER_INPUTS"                                        : "1"                                          ,
        "bool RX_PAYLOAD_EN\\[MERGER_INPUTS-1:0\\]"            : "{TRUE}"                                     ,
        "int unsigned RX_MVB_SRC_RDY_FALL_CHANCE  \\[\\]"      : "{50}"                                       ,
        "int unsigned RX_MVB_SRC_RDY_FALL_TIME_MAX\\[\\]"      : "{15}"                                       ,
        "int unsigned RX_MFB_SRC_RDY_FALL_CHANCE  \\[\\]"      : "{33}"                                       ,
        "int unsigned RX_MFB_SRC_RDY_FALL_TIME_MAX\\[\\]"      : "{20}"                                       ,
    },
    "inputs_2_0" : {
        "MERGER_INPUTS"                                        : "2"                                          ,
        "bool RX_PAYLOAD_EN\\[MERGER_INPUTS-1:0\\]"            : "{FALSE,TRUE}"                               ,
        "int unsigned RX_MVB_SRC_RDY_FALL_CHANCE  \\[\\]"      : "{60,28}"                                    ,
        "int unsigned RX_MVB_SRC_RDY_FALL_TIME_MAX\\[\\]"      : "{15,50}"                                    ,
        "int unsigned RX_MFB_SRC_RDY_FALL_CHANCE  \\[\\]"      : "{33,44}"                                    ,
        "int unsigned RX_MFB_SRC_RDY_FALL_TIME_MAX\\[\\]"      : "{20,20}"                                    ,
    },
    "inputs_2_1" : {
        "MERGER_INPUTS"                                        : "2"                                          ,
        "bool RX_PAYLOAD_EN\\[MERGER_INPUTS-1:0\\]"            : "{FALSE,FALSE}"                              ,
        "int unsigned RX_MVB_SRC_RDY_FALL_CHANCE  \\[\\]"      : "{55,10}"                                    ,
        "int unsigned RX_MVB_SRC_RDY_FALL_TIME_MAX\\[\\]"      : "{25,20}"                                    ,
        "int unsigned RX_MFB_SRC_RDY_FALL_CHANCE  \\[\\]"      : "{33,30}"                                    ,
        "int unsigned RX_MFB_SRC_RDY_FALL_TIME_MAX\\[\\]"      : "{20,20}"                                    ,
    },
    "inputs_3_0" : {
        "MERGER_INPUTS"                                        : "3"                                          ,
        "bool RX_PAYLOAD_EN\\[MERGER_INPUTS-1:0\\]"            : "{TRUE,TRUE,TRUE}"                           ,
        "int unsigned RX_MVB_SRC_RDY_FALL_CHANCE  \\[\\]"      : "{50,22,89}"                                 ,
        "int unsigned RX_MVB_SRC_RDY_FALL_TIME_MAX\\[\\]"      : "{15,10,12}"                                 ,
        "int unsigned RX_MFB_SRC_RDY_FALL_CHANCE  \\[\\]"      : "{33,80,20}"                                 ,
        "int unsigned RX_MFB_SRC_RDY_FALL_TIME_MAX\\[\\]"      : "{20,20,10}"                                 ,
    },
    "inputs_3_1" : {
        "MERGER_INPUTS"                                        : "3"                                          ,
        "bool RX_PAYLOAD_EN\\[MERGER_INPUTS-1:0\\]"            : "{TRUE,TRUE,TRUE}"                           ,
        "int unsigned RX_MVB_SRC_RDY_FALL_CHANCE  \\[\\]"      : "{28,90,60}"                                 ,
        "int unsigned RX_MVB_SRC_RDY_FALL_TIME_MAX\\[\\]"      : "{15,12,10}"                                 ,
        "int unsigned RX_MFB_SRC_RDY_FALL_CHANCE  \\[\\]"      : "{33,66,84}"                                 ,
        "int unsigned RX_MFB_SRC_RDY_FALL_TIME_MAX\\[\\]"      : "{20,10,10}"                                 ,
    },
    "inputs_5_0" : {
        "MERGER_INPUTS"                                        : "5"                                          ,
        "bool RX_PAYLOAD_EN\\[MERGER_INPUTS-1:0\\]"            : "{TRUE,TRUE,TRUE,TRUE,TRUE}"                 ,
        "int unsigned RX_MVB_SRC_RDY_FALL_CHANCE  \\[\\]"      : "{20,32,40,58,26}"                           ,
        "int unsigned RX_MVB_SRC_RDY_FALL_TIME_MAX\\[\\]"      : "{10,20,10,20,10}"                           ,
        "int unsigned RX_MFB_SRC_RDY_FALL_CHANCE  \\[\\]"      : "{20,52,19,36,20}"                           ,
        "int unsigned RX_MFB_SRC_RDY_FALL_TIME_MAX\\[\\]"      : "{20,20,10,14,10}"                           ,
    },
    "inputs_5_1" : {
        "MERGER_INPUTS"                                        : "5"                                          ,
        "bool RX_PAYLOAD_EN\\[MERGER_INPUTS-1:0\\]"            : "{FALSE,TRUE,TRUE,FALSE,FALSE}"              ,
        "int unsigned RX_MVB_SRC_RDY_FALL_CHANCE  \\[\\]"      : "{30, 2,40,18,56}"                           ,
        "int unsigned RX_MVB_SRC_RDY_FALL_TIME_MAX\\[\\]"      : "{25,25,16,20,10}"                           ,
        "int unsigned RX_MFB_SRC_RDY_FALL_CHANCE  \\[\\]"      : "{20,12,29,36,11}"                           ,
        "int unsigned RX_MFB_SRC_RDY_FALL_TIME_MAX\\[\\]"      : "{20,25,10,14,14}"                           ,
    },

    "mvb_1" : {
        "MVB_ITEMS"      : "2" ,
        "MVB_ITEM_WIDTH" : "19",
    },
    "mvb_4" : {
        "MVB_ITEMS"      : "4" ,
        "MVB_ITEM_WIDTH" : "17",
    },

    "mfb_pcie" : {
        "MFB_REGIONS"    : "2" ,
        "MFB_REG_SIZE"   : "1" ,
        "MFB_BLOCK_SIZE" : "8" ,
        "MFB_ITEM_WIDTH" : "32",
        "MFB_META_WIDTH" : "5" ,
    },
    "mfb_0" : {
        "MFB_REGIONS"    : "1" ,
        "MFB_REG_SIZE"   : "2" ,
        "MFB_BLOCK_SIZE" : "2" ,
        "MFB_ITEM_WIDTH" : "4" ,
        "MFB_META_WIDTH" : "8" ,
    },
    "mfb_1" : {
        "MFB_REGIONS"    : "4" ,
        "MFB_REG_SIZE"   : "2" ,
        "MFB_BLOCK_SIZE" : "1" ,
        "MFB_ITEM_WIDTH" : "8" ,
        "MFB_META_WIDTH" : "8" ,
    },
    "mfb_2" : {
        "MFB_REGIONS"    : "8" ,
        "MFB_REG_SIZE"   : "8" ,
        "MFB_BLOCK_SIZE" : "4" ,
        "MFB_ITEM_WIDTH" : "4" ,
        "MFB_META_WIDTH" : "81",
    },

    "big_in_fifo" : {
        "INPUT_FIFO_SIZE" : "64",
    },

    "in_pipe" : {
        "IN_PIPE_EN" : "TRUE",
    },

    "out_pipe" : {
        "OUT_PIPE_EN" : "TRUE",
    },

    "device_stratix" : {
        "DEVICE" : "\\\"STRATIX10\\\"",
    },

    "slow_tx" : {
        "TX_MVB_DST_RDY_FALL_CHANCE"   : "83",
        "TX_MVB_DST_RDY_FALL_TIME_MAX" : "24",
        "TX_MFB_DST_RDY_FALL_CHANCE"   : "62",
        "TX_MFB_DST_RDY_FALL_TIME_MAX" : "22",
    },

    "verbose" : {
        "FULL_PRINT" : "TRUE",
    },

    "_combinations_" : (
    ("default",),

    (             "mvb_1",                         "in_pipe",           "device_stratix",          ),
    (                     "mfb_0"   ,                        "out_pipe","device_stratix",          ),
    (                                                        "out_pipe",                           ),
    (             "mvb_4","mfb_1"   ,                                                    "slow_tx",),
    (             "mvb_1","mfb_2"   ,"big_in_fifo","in_pipe","out_pipe",                 "slow_tx",),
    (                     "mfb_pcie","big_in_fifo",          "out_pipe",                 "slow_tx",),
    (                     "mfb_pcie","big_in_fifo",                                                ),
    (                     "mfb_0"   ,                        "out_pipe","device_stratix",          ),
    (             "mvb_1","mfb_2"   ,              "in_pipe",           "device_stratix",          ),
    (             "mvb_4","mfb_pcie",              "in_pipe",           "device_stratix","slow_tx",),

    ("inputs_1_0","mvb_1",                         "in_pipe",           "device_stratix",          ),
    ("inputs_1_0",        "mfb_0"   ,                        "out_pipe","device_stratix",          ),
    ("inputs_1_0",                                           "out_pipe",                           ),
    ("inputs_1_0","mvb_4","mfb_1"   ,                                                    "slow_tx",),
    ("inputs_1_0","mvb_1","mfb_2"   ,"big_in_fifo","in_pipe","out_pipe",                 "slow_tx",),
    ("inputs_1_0",        "mfb_pcie","big_in_fifo",          "out_pipe",                 "slow_tx",),
    ("inputs_1_0",        "mfb_pcie","big_in_fifo",                                                ),
    ("inputs_1_0",        "mfb_0"   ,                        "out_pipe","device_stratix",          ),
    ("inputs_1_0","mvb_1","mfb_2"   ,              "in_pipe",           "device_stratix",          ),
    ("inputs_1_0","mvb_4","mfb_pcie",              "in_pipe",           "device_stratix","slow_tx",),

    ("inputs_2_0","mvb_1",                         "in_pipe",           "device_stratix",          ),
    ("inputs_2_0",        "mfb_0"   ,                        "out_pipe","device_stratix",          ),
    ("inputs_2_0",                                           "out_pipe",                           ),
    ("inputs_2_0","mvb_4","mfb_1"   ,                                                    "slow_tx",),
    ("inputs_2_0","mvb_1","mfb_2"   ,"big_in_fifo","in_pipe","out_pipe",                 "slow_tx",),
    ("inputs_2_0",        "mfb_pcie","big_in_fifo",          "out_pipe",                 "slow_tx",),
    ("inputs_2_0",        "mfb_pcie","big_in_fifo",                                                ),
    ("inputs_2_0",        "mfb_0"   ,                        "out_pipe","device_stratix",          ),
    ("inputs_2_0","mvb_1","mfb_2"   ,              "in_pipe",           "device_stratix",          ),
    ("inputs_2_0","mvb_4","mfb_pcie",              "in_pipe",           "device_stratix","slow_tx",),

    ("inputs_2_1","mvb_1",                         "in_pipe",           "device_stratix",          ),
    ("inputs_2_1",        "mfb_0"   ,                        "out_pipe","device_stratix",          ),
    ("inputs_2_1",                                           "out_pipe",                           ),
    ("inputs_2_1","mvb_4","mfb_1"   ,                                                    "slow_tx",),
    ("inputs_2_1","mvb_1","mfb_2"   ,"big_in_fifo","in_pipe","out_pipe",                 "slow_tx",),
    ("inputs_2_1",        "mfb_pcie","big_in_fifo",          "out_pipe",                 "slow_tx",),
    ("inputs_2_1",        "mfb_pcie","big_in_fifo",                                                ),
    ("inputs_2_1",        "mfb_0"   ,                        "out_pipe","device_stratix",          ),
    ("inputs_2_1","mvb_1","mfb_2"   ,              "in_pipe",           "device_stratix",          ),
    ("inputs_2_1","mvb_4","mfb_pcie",              "in_pipe",           "device_stratix","slow_tx",),

    ("inputs_3_0","mvb_1",                         "in_pipe",           "device_stratix",          ),
    ("inputs_3_0",        "mfb_0"   ,                        "out_pipe","device_stratix",          ),
    ("inputs_3_0",                                           "out_pipe",                           ),
    ("inputs_3_0","mvb_4","mfb_1"   ,                                                    "slow_tx",),
    ("inputs_3_0","mvb_1","mfb_2"   ,"big_in_fifo","in_pipe","out_pipe",                 "slow_tx",),
    ("inputs_3_0",        "mfb_pcie","big_in_fifo",          "out_pipe",                 "slow_tx",),
    ("inputs_3_0",        "mfb_pcie","big_in_fifo",                                                ),
    ("inputs_3_0",        "mfb_0"   ,                        "out_pipe","device_stratix",          ),
    ("inputs_3_0","mvb_1","mfb_2"   ,              "in_pipe",           "device_stratix",          ),
    ("inputs_3_0","mvb_4","mfb_pcie",              "in_pipe",           "device_stratix","slow_tx",),

    ("inputs_3_1","mvb_1",                         "in_pipe",           "device_stratix",          ),
    ("inputs_3_1",        "mfb_0"   ,                        "out_pipe","device_stratix",          ),
    ("inputs_3_1",                                           "out_pipe",                           ),
    ("inputs_3_1","mvb_4","mfb_1"   ,                                                    "slow_tx",),
    ("inputs_3_1","mvb_1","mfb_2"   ,"big_in_fifo","in_pipe","out_pipe",                 "slow_tx",),
    ("inputs_3_1",        "mfb_pcie","big_in_fifo",          "out_pipe",                 "slow_tx",),
    ("inputs_3_1",        "mfb_pcie","big_in_fifo",                                                ),
    ("inputs_3_1",        "mfb_0"   ,                        "out_pipe","device_stratix",          ),
    ("inputs_3_1","mvb_1","mfb_2"   ,              "in_pipe",           "device_stratix",          ),
    ("inputs_3_1","mvb_4","mfb_pcie",              "in_pipe",           "device_stratix","slow_tx",),

    ("inputs_5_0","mvb_1",                         "in_pipe",           "device_stratix",          ),
    ("inputs_5_0",        "mfb_0"   ,                        "out_pipe","device_stratix",          ),
    ("inputs_5_0",                                           "out_pipe",                           ),
    ("inputs_5_0","mvb_4","mfb_1"   ,                                                    "slow_tx",),
    ("inputs_5_0","mvb_1","mfb_2"   ,"big_in_fifo","in_pipe","out_pipe",                 "slow_tx",),
    ("inputs_5_0",        "mfb_pcie","big_in_fifo",          "out_pipe",                 "slow_tx",),
    ("inputs_5_0",        "mfb_pcie","big_in_fifo",                                                ),
    ("inputs_5_0",        "mfb_0"   ,                        "out_pipe","device_stratix",          ),
    ("inputs_5_0","mvb_1","mfb_2"   ,              "in_pipe",           "device_stratix",          ),
    ("inputs_5_0","mvb_4","mfb_pcie",              "in_pipe",           "device_stratix","slow_tx",),

    ("inputs_5_1","mvb_1",                         "in_pipe",           "device_stratix",          ),
    ("inputs_5_1",        "mfb_0"   ,                        "out_pipe","device_stratix",          ),
    ("inputs_5_1",                                           "out_pipe",                           ),
    ("inputs_5_1","mvb_4","mfb_1"   ,                                                    "slow_tx",),
    ("inputs_5_1","mvb_1","mfb_2"   ,"big_in_fifo","in_pipe","out_pipe",                 "slow_tx",),
    ("inputs_5_1",        "mfb_pcie","big_in_fifo",          "out_pipe",                 "slow_tx",),
    ("inputs_5_1",        "mfb_pcie","big_in_fifo",                                                ),
    ("inputs_5_1",        "mfb_0"   ,                        "out_pipe","device_stratix",          ),
    ("inputs_5_1","mvb_1","mfb_2"   ,              "in_pipe",           "device_stratix",          ),
    ("inputs_5_1","mvb_4","mfb_pcie",              "in_pipe",           "device_stratix","slow_tx",),

    ),

    # Only run random 30% of the combinations
    "_combinations_run_percentage_" : 30,
}
