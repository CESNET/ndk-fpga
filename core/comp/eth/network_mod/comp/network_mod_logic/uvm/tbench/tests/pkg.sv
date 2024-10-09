// pkg.sv: Test package
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kondys <xkondy00@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause 

`ifndef SPLITTER_SIMPLE_TEST_SV
`define SPLITTER_SIMPLE_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter ETH_CHANNELS = 4;
    parameter ETH_PORT_ID = 0;

    // USER_REGIONS*USER_REGION_SIZE = 2*CORE_REGIONS*CORE_REGION_SIZE
    parameter USER_REGIONS = 2;
    parameter USER_REGION_SIZE = 8;
    parameter CORE_REGIONS = 1;
    parameter CORE_REGION_SIZE = 8;
    parameter BLOCK_SIZE = 8;
    parameter ITEM_WIDTH = 8;

    //                           ETH_TX_HDR_DISCARD_W + ETH_TX_HDR_PORT_W + ETH_TX_HDR_LENGTH_W
    parameter ETH_TX_HDR_WIDTH = 1                    + 8                 + 16                 ; // =25
    parameter META_WIDTH = ETH_TX_HDR_WIDTH;   // Note that this width must be great enought to map all splitter outputs
    //                           ETH_RX_HDR_TIMESTAMP_W + ETH_RX_HDR_TIMESTAMPVLD_W + ETH_RX_HDR_HITMAC_W + ETH_RX_HDR_HITMACVLD_W -> ETH_RX_HDR_ERROR_W + ETH_RX_HDR_PORT_W + ETH_RX_HDR_LENGTH_W
    parameter ETH_RX_HDR_WIDTH = 64                     + 1                         + 4                   + 9*1                                          + 8                 + 16; // = 102
    parameter USER_MVB_WIDTH = ETH_RX_HDR_WIDTH;

    parameter MI_DATA_WIDTH = 32;
    parameter MI_ADDR_WIDTH = 32;

    parameter RESET_USER_WIDTH = 8;
    parameter RESET_CORE_WIDTH = ETH_CHANNELS*2;

    parameter DEVICE = "AGILEX";
    parameter BOARD = "DK-DEV-1SDX-P"; // 400G1, DK-DEV-AGI027RES, DK-DEV-1SDX-P
    parameter RESIZE_BUFFER = 1'b1;
    parameter RX_MAC_LITE_REGIONS = (RESIZE_BUFFER == 1'b1) ? 2*CORE_REGIONS : CORE_REGIONS;

    parameter DRAIN_TIME = 20ns;
    parameter TRANSACTION_COUNT = 1000;

    parameter CLK_PERIOD_USER = 5ns;
    parameter CLK_PERIOD_CORE = 2.5ns;

    parameter RESET_CLKS = 10;

    `include "sequence.sv"
    `include "test.sv"

endpackage
`endif
