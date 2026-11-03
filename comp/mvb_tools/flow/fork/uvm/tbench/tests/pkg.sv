// pkg.sv: Test package
// MVB_FORK UVM verification
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

`ifndef MVB_FORK_UVM_TEST_SV
`define MVB_FORK_UVM_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter OUTPUT_PORTS = 2;

    parameter ITEMS        = 1;
    parameter ITEM_WIDTH   = 8;
    parameter USE_DST_RDY  = 1;
    parameter VERSION      = "simple";

    parameter REPEAT = 20;

    parameter CLK_PERIOD = 10ns;
    parameter RESET_CLKS = 10;

    `include "sequence.sv"
    `include "test.sv"

endpackage
`endif
