# ver_settings.py
# Copyright (C) 2019 CESNET z. s. p. o.
# Author(s): Jan Kubalek <xkubal11@stud.fit.vutbr.cz>
#
# SPDX-License-Identifier: BSD-3-Clause

SETTINGS = {
    "default" : { # The default setting of verification
        "TRANSACTIONS"           : "2048"           ,
        "TRANS_LENGTH_MIN"       : "1"              ,
        "TRANS_LENGTH_MAX"       : "256"            ,
        "TRANS_GAP_LENGTH_MIN"   : "0"              ,
        "TRANS_GAP_LENGTH_MAX"   : "128"            ,
        "RX_TRANS_NOT_RDY_CH"    : "10"             ,
        "TX_TRANS_NOT_RDY_CH"    : "10"             ,
        "TRANS_AB_ALIGNED_CH"    : "10"             ,
        "TRANS_START_ALIGNED_CH" : "10"             ,
        "DATA_DIR"               : "true"           ,
        "USE_CLK2"               : "true"           ,
        "USE_CLK_ARB"            : "false"          ,
        "TRANS_STREAMS"          : "1"              ,
        "BUF_A_STREAM_ROWS"      : "1"              ,
        "BUF_B_ROWS"             : "1*TRANS_STREAMS",
        "BUF_A_SECTIONS"         : "1"              ,
        "BUF_B_SECTIONS"         : "1"              ,
        "ROW_ITEMS"              : "1"              ,
        "ITEM_WIDTH"             : "8"              ,
        "TRANSS"                 : "1"              ,
        "TRANS_FIFO_ITEMS"       : "TRANSS*16"      ,
        "RD_LATENCY"             : "1"              ,
        "DATA_MUX_LAT"           : "0"              ,
        "DATA_MUX_OUTREG_EN"     : "true"           ,
        "DATA_ROT_LAT"           : "0"              ,
        "DATA_ROT_OUTREG_EN"     : "true"           ,
    },
    "2_streams" : { #
        "TRANS_STREAMS"          : "2"              ,
    },
    "4_streams" : { #
        "TRANS_STREAMS"          : "4"              ,
    },
    "2_transs" : { #
        "TRANSS"                 : "2"              ,
    },
    "4_transs" : { #
        "TRANSS"                 : "4"              ,
    },
    "4_a_sections" : { #
        "BUF_A_SECTIONS"         : "4"              ,
    },
    "4_b_sections" : { #
        "BUF_B_SECTIONS"         : "4"              ,
    },
    "2_row_items" : { #
        "ROW_ITEMS"              : "2"              ,
    },
    "4_row_items" : { #
        "ROW_ITEMS"              : "4"              ,
    },
    "2_a_rows" : { #
        "BUF_A_STREAM_ROWS"      : "2"              ,
    },
    "2_b_rows" : { #
        "BUF_B_ROWS"             : "2"              ,
    },
    "4_b_rows" : { #
        "BUF_B_ROWS"             : "4"              ,
    },
    "low_dst_rdy" : { # Extremely low DST_RDY
        "TX_TRANS_NOT_RDY_CH"    : "80"             ,
        "TRANSACTIONS"           : "512"            ,
    },
    "thr" : { # Max throughput test
        "TRANS_LENGTH_MIN"       : "8"              ,
        "TRANS_LENGTH_MAX"       : "256"            ,
        "TRANS_GAP_LENGTH_MIN"   : "0"              ,
        "TRANS_GAP_LENGTH_MAX"   : "0"              ,
        "RX_TRANS_NOT_RDY_CH"    : "0"              ,
        "TX_TRANS_NOT_RDY_CH"    : "0"              ,
        "TRANS_AB_ALIGNED_CH"    : "100"            ,
        "TRANS_START_ALIGNED_CH" : "100"            ,
        "TRANS_STREAMS"          : "2"              ,
        "BUF_A_STREAM_ROWS"      : "4"              ,
        "BUF_B_ROWS"             : "4*TRANS_STREAMS",
        "BUF_A_SECTIONS"         : "1"              ,
        "BUF_B_SECTIONS"         : "1"              ,
        "TRANSS"                 : "2"              ,
    },
    "cross_latency" : { # Increased Crossbar latency
        "RD_LATENCY"             : "4"              ,
        "DATA_MUX_LAT"           : "4"              ,
        "DATA_MUX_OUTREG_EN"     : "false"          ,
        "DATA_ROT_LAT"           : "4"              ,
        "DATA_ROT_OUTREG_EN"     : "false"          ,
    },
    "reversed_data_dir" : { # Reversed Data Direction
        "DATA_DIR"               : "false"          ,
    },
    "no_clk2" : { # Don't use double CLK
        "USE_CLK2"               : "false"          ,
    },
    "clk_arb" : { # Use arbitrary CLK
        "USE_CLK_ARB"            : "true"           ,
    },
#    "" : { #
#    },
    "_combinations_" : (
    # basic tests
    ("default"          ,),
    ("2_streams"        ,),
    ("4_streams"        ,),
    ("2_transs"         ,),
    ("4_transs"         ,),
    ("4_a_sections"     ,),
    ("4_b_sections"     ,),
    ("2_row_items"      ,),
    ("4_row_items"      ,),
    ("2_a_rows"         ,),
    ("2_b_rows"         ,),
    ("4_b_rows"         ,),
    ("low_dst_rdy"      ,),
    ("thr"              ,),
    ("cross_latency"    ,),
    ("reversed_data_dir",),
    ("no_clk2"          ,),
    ("clk_arb"          ,),

    # easy test
    ("2_transs","2_a_rows","2_b_rows","2_row_items"),
    # multiple sections
    ("4_a_sections","4_b_sections","2_transs","2_row_items"),
    # wider A
    ("2_streams","2_a_rows","4_row_items"),
    # wider B
    ("2_streams","2_a_rows","4_b_rows","4_row_items"),
    # reversed direction test
    ("2_transs","2_a_rows","2_b_rows","2_row_items","reversed_data_dir"),
    # complicated test
    ("4_a_sections","4_b_sections","4_streams","4_transs","2_a_rows","4_b_rows","4_row_items"),
    # complicated test with reversed data direction
    ("4_a_sections","4_b_sections","4_streams","4_transs","2_a_rows","4_b_rows","4_row_items","reversed_data_dir"),
    # complicated test with reversed data direction and arbitrary clock
    ("4_a_sections","4_b_sections","4_streams","4_transs","2_a_rows","4_b_rows","4_row_items","reversed_data_dir","clk_arb"),
    )
}
