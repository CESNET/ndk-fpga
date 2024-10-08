//-- pkg.sv: Test package
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef FIFOX_TEST_SV
`define FIFOX_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter REGIONS          = 2;
    parameter REGION_SIZE      = 8;
    parameter BLOCK_SIZE       = 8;
    parameter ITEM_WIDTH       = 8;
    parameter CNT_TICKS_WIDTH  = 24;
    parameter CNT_BYTES_WIDTH  = 32;
    parameter MI_DATA_WIDTH    = 32;
    parameter MI_ADDRESS_WIDTH = 32;

    // configure space between packet
    parameter SPACE_SIZE_MIN_RX = 1;
    parameter SPACE_SIZE_MAX_RX = 1;
    parameter SPACE_SIZE_MIN_TX = 1;
    parameter SPACE_SIZE_MAX_TX = 1;

    parameter CLK_PERIOD        = 4ns;
    parameter RESET_CLKS        = 10;

    `include "sequence.sv"
    `include "test.sv"

endpackage
`endif
