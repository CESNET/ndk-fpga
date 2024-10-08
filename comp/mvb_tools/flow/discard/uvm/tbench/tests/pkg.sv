//-- pkg.sv: Test package
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author:   Jakub Cabal <cabal@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef FIFOX_TEST_SV
`define FIFOX_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter ITEM_WIDTH = 77;
    parameter ITEMS = 1;

    parameter REPEAT = 20;

    parameter CLK_PERIOD = 4ns;

    parameter RESET_CLKS = 10;

    `include "sequence.sv"
    `include "test.sv"

endpackage
`endif
