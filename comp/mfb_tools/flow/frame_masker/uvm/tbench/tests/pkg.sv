// pkg.sv: Test package
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kondys <kondys@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


`ifndef FRAME_MASKER_TEST_SV
`define FRAME_MASKER_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    // Number of Regions within a data word, must be power of 2
    parameter MFB_REGIONS        = 1;
    // Region size (in Blocks)
    parameter MFB_REGION_SIZE    = 8;
    // Block size (in Items)
    parameter MFB_BLOCK_SIZE     = 8;
    // Item width (in bits)
    parameter MFB_ITEM_WIDTH     = 8;
    // Meta width (in bits)
    parameter MFB_META_WIDTH     = 8;
    // Enables MFB_PIPE on RX side
    parameter USE_PIPE           = 0;

    parameter FRAME_SIZE_MIN     = 60;
    parameter FRAME_SIZE_MAX     = 1500;

    parameter CLK_PERIOD         = 4ns;

    parameter RESET_CLKS         = 10;

    `include "sequence.sv"
    `include "test.sv"
    `include "speed.sv"
endpackage
`endif
