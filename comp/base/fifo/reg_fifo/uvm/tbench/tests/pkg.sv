// pkg.sv: Test package
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

`ifndef FIFO_REGISTERED_TEST_SV
`define FIFO_REGISTERED_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter DATA_WIDTH = 16;
    parameter ITEMS      = 16;
    parameter FAKE_FIFO  = 0;

    parameter MIN_TRANSACTION_COUNT = 4000;
    parameter MAX_TRANSACTION_COUNT = 10000;

    parameter CLK_PERIOD = 4ns;

    `include "sequence.sv"
    `include "test.sv"

endpackage

`endif
