// crossbarx_stream.vhd: Crossbarx stream
// Copyright (C) 2020 CESNET z. s. p. o.
// Author(s): Daniel Kriz <xkrizd01@vutbr.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

package test_pkg;

    import math_pkg::*;

    parameter CX_USE_CLK2    = 0;
    parameter CX_USE_CLK_ARB = 1; // has priority over CX_USE_CLK2

    // set to 1 when TX CLK should be the same as RX CLK
    parameter OBUF_META_EQ_OUTPUT  = 1;
    // set to 1 when TX CLK should be the same as CLK used on CX data interfaces, set by CX_USE_CLK2 and CX_USE_CLK_ARB
    parameter OBUF_INPUT_EQ_OUTPUT = 0;

    parameter MFB_REGIONS     = 2;
    parameter MFB_REGION_SIZE = 1;
    parameter MFB_BLOCK_SIZE  = 8;
    parameter MFB_ITEM_WIDTH  = 32;
    parameter MFB_META_WIDTH  = 129;
    parameter EXT_META_WIDTH  = MFB_META_WIDTH+1;

    // ModelSim throws errors for PKT_MTU > 2**13, available fixup in top_level.fdo
    parameter PKT_MTU         = 2**12;
    parameter TRANS_FIFO_SIZE = 64;

    // Generator parameters
    parameter FRAME_SIZE_MAX = PKT_MTU;
    parameter FRAME_SIZE_MIN = MFB_REGION_SIZE*MFB_BLOCK_SIZE;

    parameter F_GAP_ADJUST_EN           = 1;
    // MUST be greater or equal to F_GAP_ADJUST_SIZE_MIN!
    parameter F_GAP_ADJUST_SIZE_AVG     = 20;
    // MUST be greater or equal to MFB_BLOCK_SIZE!
    parameter F_GAP_ADJUST_SIZE_MIN     = 17;
    // The number of gaps from which the average is calculated
    parameter AVG_GAP_SIZE_CHECK_PERIOD = 100;

    parameter F_EXTEND_START_EN     = 1;
    // in MFB ITEMS, negative number for packet shrinking
    parameter F_EXTEND_START_SIZE   = 100;

    parameter F_EXTEND_END_EN       = 1;
    // in MFB ITEMS, negative number for packet shrinking
    parameter F_EXTEND_END_SIZE     = -4;

    // Chance of gaps between src_rdy
    parameter SRC_RDY_OFF_CHANCE   = 20;
    // Maximum amount of clock cycles, when src_rdy is asserted
    parameter SRC_RDY_OFF_TIME_MAX = 10;
    // Maximum amount of clock cycles, when src_rdy is deasserted
    parameter SRC_RDY_ON_TIME_MAX  = 10;

    // Chance of gaps between src_rdy
    parameter DST_RDY_OFF_CHANCE   = 80;
    // Maximum amount of clock cycles, when src_rdy is asserted
    parameter DST_RDY_OFF_TIME_MAX = 10;
    // Maximum amount of clock cycles, when src_rdy is deasserted
    parameter DST_RDY_ON_TIME_MAX  = 10;

    // Discard settings
    parameter DISCARD = 0; // 0 = disabled, 1 = random, 2 = always asserted

    // MFB speed measure settings
    parameter THROUGHPUT_MEAS_EN    = 0;
    parameter RX_MFB_SPEED_DELAY    = 1000;
    parameter TX_MFB_SPEED_DELAY    = 1000;

    // Clock and reset parameters
    parameter RX_CLK_PERIOD  = 5ns;
    parameter TX_CLK_PERIOD  = 5ns;
    parameter CLK_ARB_PERIOD = 1.7*RX_CLK_PERIOD;
    parameter RESET_TIME     = 10*RX_CLK_PERIOD;

    // VERBOSE = 0 show only current count of recieved transactions
    // VERBOSE = 1 also show information about packet drop
    // VERBOSE = 2 show that the transaction has been inserted into the table and received by the monitor
    // VERBOSE = 3 provide all the info
    parameter VERBOSE = 0;

    parameter TRANSACTION_COUNT = 2000;

    parameter DEVICE = "STRATIX10"; // STRATIX10, ULTRASCALE, ..

    `include "scoreboard.sv"

endpackage
