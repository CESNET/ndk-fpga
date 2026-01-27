// pkg.sv: Test package
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

`ifndef MVB_MERGE_STREAMS_TEST_SV
`define MVB_MERGE_STREAMS_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter MVB_ITEMS       = 4;
    parameter MVB_ITEM_WIDTH  = 32;
    parameter RX_STREAMS      = 2;
    parameter RX_SHAKEDOWN_EN = 1;
    parameter SW_TIMEOUT_W    = 4;

    parameter DEVICE = "AGILEX";

    parameter time CLK_PERIOD = 4ns;

    `include "data_sequence.sv"
    `include "virtual_sequence_base.sv"
    `include "test_base.sv"
    `include "test_speed.sv"

endpackage

`endif
