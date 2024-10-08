// pkg.sv: parameter pkgs
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


`ifndef RX_MAC_LITE_BUFFER_TEST_PARAM_SV
`define RX_MAC_LITE_BUFFER_TEST_PARAM_SV

package test_param;

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
    parameter MFB_META_WIDTH     = 131;
    parameter DEVICE             = "AGILEX";

    parameter RX_CLK_PERIOD     = 2.4ns;
    parameter TX_CLK_PERIOD     = 5ns;

    parameter FRAME_SIZE_MIN     = 1;
    parameter FRAME_SIZE_MAX     = 1500;
endpackage
`endif
