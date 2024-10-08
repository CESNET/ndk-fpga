// pkg.sv: Test package
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kříž <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


`ifndef SUPERUNPACKETER_TEST_SV
`define SUPERUNPACKETER_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    // Number of Regions within a data word, must be power of 2.
    parameter MFB_REGIONS        = 32;
    // Region size (in Blocks).
    parameter MFB_REGION_SIZE    = 4;
    // Block size (in Items), must be 8.
    parameter MFB_BLOCK_SIZE     = 8;
    // Item width (in bits), must be 8.
    parameter MFB_ITEM_WIDTH     = 8;
    parameter MFB_META_WIDTH     = 8;
    // MVB ITEMS
    parameter MVB_ITEMS          = 2;
    parameter MVB_ITEM_WIDTH     = 8;
    // FPGA device name: ULTRASCALE, STRATIX10, AGILEX, ...
    parameter INSERT_MODE        = 1;
    // 0 SOF, 1 EOF
    parameter MFB_META_ALIGNMENT = 1;
    parameter MVB_FIFO_SIZE      = 4;
    parameter DEVICE             = "ULTRASCALE";

    parameter FRAME_SIZE_MIN     = 32;
    parameter FRAME_SIZE_MAX     = 512;

    parameter CLK_PERIOD         = 4ns;

    parameter RESET_CLKS         = 10;

    `include "sequence.sv"
    `include "test.sv"
    `include "speed.sv"
endpackage
`endif
