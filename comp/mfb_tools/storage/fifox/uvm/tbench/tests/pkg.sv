// pkg.sv: Test package
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Mikuláš Brázda <xbrazd21@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


`ifndef MFB_FIFOX
`define MFB_FIFOX

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter REGIONS            = 1;
    parameter REGION_SIZE        = 2;
    parameter BLOCK_SIZE         = 4;
    parameter ITEM_WIDTH         = 8;
    parameter FIFO_DEPTH         = 42;
    parameter RAM_TYPE           = "AUTO";
    parameter DEVICE             = "ULTRASCALE";
    parameter META_WIDTH         = 42;

    parameter DRAIN_TIME         = 20ns;
    parameter TRANSACTION_COUNT  = 1000000;

    parameter CLK_PERIOD         = 2500ps;

    parameter RESET_CLKS         = 10;

    `include "sequence.sv"
    `include "test.sv"
endpackage
`endif
