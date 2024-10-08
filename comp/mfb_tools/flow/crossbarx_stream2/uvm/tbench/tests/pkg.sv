// pkg.sv: Test package
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


`ifndef MFB_CROSSBARX_STREAM2_TEST_SV
`define MFB_CROSSBARX_STREAM2_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter RX_MFB_REGIONS  = 4;
    parameter RX_MFB_REGION_S = 8;
    parameter RX_MFB_BLOCK_S  = 8;
    parameter RX_MFB_ITEM_W   = 8;

    parameter TX_MFB_REGIONS  = RX_MFB_REGIONS;
    parameter TX_MFB_REGION_S = RX_MFB_REGION_S;
    parameter TX_MFB_BLOCK_S  = RX_MFB_BLOCK_S;
    parameter TX_MFB_ITEM_W   = RX_MFB_ITEM_W;

    parameter USERMETA_W      = 32;
    parameter MOD_W           = 7;
    parameter RX_MVB_ITEM_W   = USERMETA_W + MOD_W + MOD_W + 5;

    parameter DEVICE          = "AGILEX";

    parameter FRAME_SIZE_MIN  = 4096;
    parameter FRAME_SIZE_MAX  = 8192;

    parameter CLK_PERIOD      = 4ns;
    parameter RESET_CLKS      = 10;

    `include "sequence.sv"
    `include "test.sv"
    `include "speed.sv"
endpackage
`endif
