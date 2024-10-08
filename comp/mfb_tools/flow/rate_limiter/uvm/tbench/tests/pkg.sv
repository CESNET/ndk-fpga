// pkg.sv: Test package
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Tomas Hak <xhakto01@vut.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef RATE_LIMITER_TEST_SV
`define RATE_LIMITER_TEST_SV

package test;
    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter MI_DATA_WIDTH   = 32;
    parameter MI_ADDR_WIDTH   = 32;

    parameter MFB_REGIONS     = 1;
    parameter MFB_REGION_SIZE = 8;
    parameter MFB_BLOCK_SIZE  = 8;
    parameter MFB_ITEM_WIDTH  = 8;
    parameter MFB_META_WIDTH  = 8;

    parameter SECTION_LENGTH  = 1000;
    parameter INTERVAL_LENGTH = 40;
    parameter INTERVAL_COUNT  = 32;
    parameter SHAPING_TYPE    = 0;
    parameter OUTPUT_SPEED    = 62500;
    parameter FREQUENCY       = 200;
    parameter DEVICE          = "AGILEX";

    parameter CLK_PERIOD      = 2500ps;

    `include "sequence.sv"
    `include "test.sv"
endpackage
`endif
