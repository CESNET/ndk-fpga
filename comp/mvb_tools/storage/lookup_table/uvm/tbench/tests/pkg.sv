//-- pkg.sv: Test package
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef LOOKUP_TABLE_TEST_SV
`define LOOKUP_TABLE_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter MVB_ITEMS       = 1;
    parameter LUT_DEPTH       = 128;
    parameter LUT_WIDTH       = 64;
    // LUT, BRAM, AUTO
    parameter LUT_ARCH        = "BRAM";
    parameter SW_WIDTH        = 32;
    parameter META_WIDTH      = 32;
    parameter OUTPUT_REG      = 0;
    parameter DEVICE          = "AGILEX";

    parameter SLICE_WIDTH     = $clog2(LUT_WIDTH/SW_WIDTH);
    parameter SLICES          = ($clog2(LUT_WIDTH/SW_WIDTH) == 0) ? 1 : $clog2(LUT_WIDTH/SW_WIDTH);
    parameter TRUE_LUT_DEPTH  = ($clog2(LUT_DEPTH) == 0) ? 1 : $clog2(LUT_DEPTH);
    parameter ADDR_DEPTH_UP   = ($clog2(LUT_WIDTH/SW_WIDTH) == 0) ? TRUE_LUT_DEPTH+2   : TRUE_LUT_DEPTH+2+SLICES;
    parameter ADDR_DEPTH_DOWN = ($clog2(LUT_WIDTH/SW_WIDTH) == 0) ? TRUE_LUT_DEPTH+2-1 : TRUE_LUT_DEPTH+2;

    parameter REG_DEPTH       = TRUE_LUT_DEPTH+2+SLICE_WIDTH;
    parameter ADDR_WIDTH      = LUT_DEPTH*(LUT_WIDTH/SW_WIDTH);

    parameter REPEAT          = 20;
    parameter CLK_PERIOD      = 4ns;
    parameter RESET_CLKS      = 10;

    `include "sequence.sv"
    `include "test.sv"

endpackage
`endif
