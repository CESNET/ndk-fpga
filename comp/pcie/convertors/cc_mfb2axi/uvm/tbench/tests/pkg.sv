//-- pkg.sv: Test package
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef FIFOX_TEST_SV
`define FIFOX_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter MFB_REGIONS      = 1;
    parameter MFB_REGION_SIZE  = 1;
    parameter MFB_BLOCK_SIZE   = 8;
    parameter MFB_ITEM_WIDTH   = 32;
    parameter MFB_REGION_WIDTH = MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH;

    parameter CC_TUSER_WIDTH   = 33;
    parameter CC_TDATA_WIDTH   = MFB_REGIONS*MFB_REGION_WIDTH;
    parameter STRADDLING       = 0;
    parameter DEVICE           = "ULTRASCALE";

    parameter CLK_PERIOD = 5ns;

    parameter RESET_CLKS = 10;

    `include "sequence.sv"
    `include "test.sv"

endpackage
`endif
