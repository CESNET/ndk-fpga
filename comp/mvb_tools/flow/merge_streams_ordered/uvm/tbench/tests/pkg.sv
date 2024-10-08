// pkg.sv: Test package
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef MVB_MERGE_STREAMS_ORDERED_TEST_SV
`define MVB_MERGE_STREAMS_ORDERED_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    // DUT settings
    parameter MVB_ITEMS         = 1;
    parameter MVB_ITEM_WIDTH    = 32;
    parameter RX_STREAMS        = 32;
    parameter USE_FIFOX_MULTI   = 1;
    parameter FIFOX_ITEMS_MULT  = 4;
    parameter SEL_SHAKEDOWN_EN  = 0;
    parameter DEVICE            = "AGILEX";

    // Verification settings
    parameter MIN_TRANSACTION_COUNT = 1000;
    parameter MAX_TRANSACTION_COUNT = 2000;
    parameter RUNS = 5;

    parameter CLK_PERIOD = 4ns;

    `include "sequence.sv"
    `include "test.sv"

endpackage
`endif
