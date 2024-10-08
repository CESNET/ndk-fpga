//-- pkg.sv: Test package
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef DROPPER_TEST_SV
`define DROPPER_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter REGIONS             = 4;
    parameter REGION_SIZE         = 8;
    parameter BLOCK_SIZE          = 8;
    parameter ITEM_WIDTH          = 8;
    parameter META_WIDTH          = 2;
    parameter EXTENDED_META_WIDTH = META_WIDTH+1;

    // configure space between packet
    parameter SPACE_SIZE_MIN_RX = 1;
    parameter SPACE_SIZE_MAX_RX = 1;
    parameter SPACE_SIZE_MIN_TX = 1;
    parameter SPACE_SIZE_MAX_TX = 1;

    parameter REPEAT          = 20;
    parameter CLK_PERIOD      = 4ns;
    parameter RESET_CLKS      = 10;

    `include "sequence.sv"
    `include "test.sv"

endpackage
`endif
