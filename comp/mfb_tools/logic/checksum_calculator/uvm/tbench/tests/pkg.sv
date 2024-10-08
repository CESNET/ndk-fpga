// pkg.sv: Test package
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

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
    // Block size (in Items), must be 8.
    parameter MFB_BLOCK_SIZE     = 8;
    // Item width (in bits), must be 8.
    parameter MFB_ITEM_WIDTH     = 8;

    parameter OFFSET_WIDTH       = 7;
    parameter LENGTH_WIDTH       = 9;
    parameter MFB_META_WIDTH     = 16;
    parameter META_WIDTH         = OFFSET_WIDTH+LENGTH_WIDTH+1+MFB_META_WIDTH;

    // Width of output checksums (in bits), other values than 16 are not supported.
    parameter MVB_DATA_WIDTH     = 16;
    // Maximum size of a packet (in Items).
    parameter PKT_MTU            = 2**12;
    // FPGA device name: ULTRASCALE, STRATIX10, AGILEX, ...
    parameter DEVICE             = "STRATIX10";

    // VERBOSITY MODE
    // 0 - None
    // 1 - Basic
    parameter VERBOSITY          = 0;

    parameter CLK_PERIOD         = 4ns;

    parameter RESET_CLKS         = 10;

    `include "sequence.sv"
    `include "test.sv"
    `include "speed.sv"
endpackage
`endif
