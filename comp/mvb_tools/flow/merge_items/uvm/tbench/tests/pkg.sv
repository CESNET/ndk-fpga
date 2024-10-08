//-- pkg.sv: Test package
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef MERGE_ITEMS_TEST_SV
`define MERGE_ITEMS_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter RX0_ITEMS      = 4;
    parameter RX0_ITEM_WIDTH = 32;

    parameter RX1_ITEMS      = 4;
    parameter RX1_ITEM_WIDTH = 16;

    parameter TX_ITEM_WIDTH  = RX0_ITEM_WIDTH+RX1_ITEM_WIDTH;

    parameter RX0_FIFO_EN    = 0;
    parameter FIFO_DEPTH     = 32;
    parameter OUTPUT_REG     = 1;

    parameter DEVICE         = "ULTRASCALE";

    parameter CLK_PERIOD     = 4ns;

    `include "single_transaction_sequence.sv"
    `include "sequence.sv"
    `include "test.sv"

endpackage
`endif
