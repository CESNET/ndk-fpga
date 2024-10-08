// pkg.sv: Test package
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef FIFOX_MULTI_TEST_SV
`define FIFOX_MULTI_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter DATA_WIDTH          = 512;
    parameter ITEMS               = 512;
    parameter WRITE_PORTS         = 4;
    parameter READ_PORTS          = 2;
    parameter RAM_TYPE            = "AUTO";
    parameter DEVICE              = "ULTRASCALE";
    parameter ALMOST_FULL_OFFSET  = 0;
    parameter ALMOST_EMPTY_OFFSET = 0;
    parameter ALLOW_SINGLE_FIFO   = 0;
    parameter SAFE_READ_MODE      = 0;

    parameter IMPL_SHAKEDOWN = 0;

    parameter MIN_TRANSACTION_COUNT = 4000;
    parameter MAX_TRANSACTION_COUNT = 5000;

    parameter CLK_PERIOD = 4ns;

    parameter ITEMS_ACTUAL = 2**$clog2(ITEMS);

    `include "sequence.sv"
    `include "test.sv"

endpackage

`endif
