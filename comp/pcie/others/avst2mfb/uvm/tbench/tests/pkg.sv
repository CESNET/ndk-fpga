//-- pkg.sv: Test package
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef PCIE_AVST2MFB_TEST_SV
`define PCIE_AVST2MFB_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter MFB_REGIONS      = 2;
    parameter MFB_REGION_SIZE  = 1;
    parameter MFB_BLOCK_SIZE   = 8;
    parameter MFB_ITEM_WIDTH   = 32;
    parameter META_WIDTH       = 128;

    parameter READY_LATENCY    = 27;
    parameter FIFO_DEPTH       = 32;
    parameter FIFO_ENABLE      = 1;
    parameter FIFO_RAM_TYPE    = "AUTO";
    parameter DEVICE           = "STRATIX10";

    parameter CLK_PERIOD = 5ns;

    parameter RESET_CLKS = 10;

    `include "sequence.sv"
    `include "test.sv"

endpackage
`endif
