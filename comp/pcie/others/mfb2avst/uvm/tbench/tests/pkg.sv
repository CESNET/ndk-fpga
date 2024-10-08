//-- pkg.sv: Test package
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef PCIE_MFB2AVST_TEST_SV
`define PCIE_MFB2AVST_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter MFB_REGIONS      = 4;
    parameter MFB_REGION_SIZE  = 1;
    parameter MFB_BLOCK_SIZE   = 8;
    parameter MFB_ITEM_WIDTH   = 32;
    parameter META_WIDTH       = 128;
    parameter READY_LATENCY    = 3;

    parameter CLK_PERIOD = 5ns;

    parameter RESET_CLKS = 10;

    `include "sequence.sv"
    `include "test.sv"

endpackage
`endif
