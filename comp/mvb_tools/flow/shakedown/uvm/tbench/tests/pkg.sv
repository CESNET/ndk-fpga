// pkg.sv: Test package
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

`ifndef MVB_SHAKEDOWN_TEST_SV
`define MVB_SHAKEDOWN_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter RX_ITEMS     = 4;
    parameter TX_ITEMS     = 1;
    parameter ITEM_WIDTH   = 128;
    parameter SHAKE_PORTS  = 2;
    parameter USE_MUX_IMPL = 0;

    parameter DEVICE = "AGILEX";

    parameter time CLK_PERIOD = 4ns;

    `include "virtual_sequence_base.sv"
    `include "test_base.sv"
    `include "virtual_sequence_speed.sv"
    `include "test_speed.sv"

endpackage

`endif
