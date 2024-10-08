// pkg.sv: Test package
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


`ifndef CHECKSUM_CALCULATOR_TEST_SV
`define CHECKSUM_CALCULATOR_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    // Number of Regions within a data word, must be power of 2.
    parameter MFB_REGIONS        = 4;
    // Region size (in Blocks).
    parameter MFB_REGION_SIZE    = 8;
    parameter MFB_BLOCK_SIZE     = 8;
    parameter MFB_ITEM_WIDTH     = 8;
    parameter MVB_DATA_WIDTH     = MFB_ITEM_WIDTH;
    parameter MVB_ITEMS          = MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE;
    // Maximum size of a packet (in Items).
    parameter PKT_MTU            = 100;
    parameter OFFSET_WIDTH       = 7;
    parameter LENGTH_WIDTH       = 7;
    parameter META_WIDTH         = OFFSET_WIDTH+LENGTH_WIDTH+1;

    parameter CLK_PERIOD         = 4ns;

    parameter RESET_CLKS         = 10;

    `include "sequence.sv"
    `include "test.sv"
    `include "speed.sv"
endpackage
`endif
