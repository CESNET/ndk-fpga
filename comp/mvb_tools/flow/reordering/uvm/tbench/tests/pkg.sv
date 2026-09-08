// pkg.sv: Test package
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

`ifndef MVB_REORDERING_TEST_SV
`define MVB_REORDERING_TEST_SV

package test;

    `include "uvm_macros.svh"
    `include "ndk_macros.svh"
    import uvm_pkg::*;

    parameter ITEMS     = 4;
    parameter ITEM_WIDTH = 64;
    parameter OUT_REG_EN = 1;
    parameter REORDERING_EN = 1;

    parameter time CLK_PERIOD = 4ns;


    `include "sequence_mvb.sv"
    `include "virtual_sequence_base.sv"
    `include "test_base.sv"

endpackage

`endif
