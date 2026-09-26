// pkg.sv: Test package
// Copyright (C) 2024 CESNET z. s. p. o.
// Author:   David Beneš <xbenes52@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef FRAMEPACKER_TEST_SV
`define FRAMEPACKER_TEST_SV

package test;

    `include "ndk_macros.svh"
    `include "uvm_macros.svh"
    import uvm_pkg::*;

    //MFB interface
    parameter MFB_REGIONS             = 4;
    parameter MFB_REGION_SIZE         = 8;
    parameter MFB_BLOCK_SIZE          = 8;
    parameter MFB_ITEM_WIDTH          = 8;
    //MFB META is not supported
    parameter MFB_META_WIDTH          = 0;

    parameter RX_CHANNELS             = 16;
    parameter HDR_META_WIDTH          = 12;
    parameter USR_RX_PKT_SIZE_MIN     = 64;
    parameter USR_RX_PKT_SIZE_MAX     = 2**14;

    // The length of Super-Packet [Bytes] the component is trying to reach
    parameter SPKT_SIZE_MIN           = 2**13;
    // Length of the timeout (4096 is an optimal value)
    parameter TIMEOUT_CLK_NO          = 2**12;

    // sequence.sv
    parameter FRAME_SIZE_MIN          = 64;
    parameter FRAME_SIZE_MAX          = 2**14 - 1;
    //MVB interface
    parameter MVB_ITEMS               = MFB_REGIONS;
    parameter MVB_TX_ITEM_WIDTH       = $clog2(RX_CHANNELS) + $clog2(USR_RX_PKT_SIZE_MAX+1) + HDR_META_WIDTH + 1;

    // Number of MFB data sequences
    parameter SEQ_MIN                 = 5;
    parameter SEQ_MAX                 = 8;
    // Probability [%] of an RX idle gap (TIMEOUT_CLK_NO/2 .. 2*TIMEOUT_CLK_NO) between the MFB data sequences
    parameter RX_GAP_PROBABILITY      = 30;
    // TX MVB DST_RDY is held low for this number of clock cycles at the beginning of the test (0 = disabled)
    parameter MVB_TX_STALL_CLKS       = 0;


    // configure space between packet
    parameter SPACE_SIZE_MIN_RX = 0;
    parameter SPACE_SIZE_MAX_RX = 0;
    parameter SPACE_SIZE_MIN_TX = 0;
    parameter SPACE_SIZE_MAX_TX = 0;

    parameter REPEAT          = 20;
    parameter CLK_PERIOD      = 5ns;
    parameter RESET_CLKS      = 10;

    `include "sequence_lib.sv"
    `include "sequence.sv"
    `include "test.sv"
    `include "speed.sv"

endpackage
`endif
