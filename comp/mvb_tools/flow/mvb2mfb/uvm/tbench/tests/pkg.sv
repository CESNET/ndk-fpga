// pkg.sv: Test package
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


`ifndef MVB2MFB_TEST_SV
`define MVB2MFB_TEST_SV

package test;

    `include "ndk_macros.svh"
    `include "uvm_macros.svh"
    import uvm_pkg::*;

    // Number of MVB items in a word.
    parameter MVB_ITEMS          = 4;
    // Width of the MVB item without the MFB metadata (in bits).
    parameter MVB_ITEM_WIDTH_RAW = 536;
    // Number of Regions within a data word, must be power of 2.
    parameter MFB_REGIONS        = 4;
    // Region size (in Blocks).
    parameter MFB_REGION_SIZE    = 8;
    // Block size (in Items).
    parameter MFB_BLOCK_SIZE     = 8;
    // Item width (in bits).
    parameter MFB_ITEM_WIDTH     = 8;
    // Alignment of the frame start (in Items).
    parameter MFB_ALIGNMENT      = MFB_REGION_SIZE*MFB_BLOCK_SIZE;
    // Width of the MFB metadata (in bits).
    parameter MFB_META_WIDTH     = 12;
    // FPGA device name: ULTRASCALE, STRATIX10, AGILEX, ...
    parameter DEVICE             = "AGILEX";

    parameter CLK_PERIOD         = 4ns;
    parameter RESET_CLKS         = 10;

    `include "sequence.sv"
    `include "test.sv"
    `include "speed.sv"
endpackage
`endif
