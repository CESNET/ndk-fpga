// pkg.sv: Test package
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef FIFOX_TEST_SV
`define FIFOX_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter DATA_WIDTH          = 16;
    parameter ITEMS               = 16;
    parameter RAM_TYPE            = "AUTO";
    parameter DEVICE              = "ULTRASCALE";
    parameter ALMOST_FULL_OFFSET  = 0;
    parameter ALMOST_EMPTY_OFFSET = 0;
    parameter FAKE_FIFO           = 0;

    parameter MIN_TRANSACTION_COUNT = 4000;
    parameter MAX_TRANSACTION_COUNT = 5000;

    parameter CLK_PERIOD = 4ns;

    parameter ITEMS_ACTUAL = (ITEMS < 2) ? 2 : ITEMS;
    parameter STATUS_WIDTH = $clog2(ITEMS_ACTUAL)+1;

    `include "sequence.sv"
    `include "test.sv"

endpackage

`endif
