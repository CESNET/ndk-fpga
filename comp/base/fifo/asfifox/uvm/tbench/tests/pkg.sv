//-- pkg.sv: Test package
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

`ifndef FIFOX_TEST_SV
`define FIFOX_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter FIFO_ITEMS = 128;
    parameter RAM_TYPE = "BRAM";
    parameter DEVICE = "ULTRASCALE";
    parameter ALMOST_FULL_OFFSET = FIFO_ITEMS/2;
    parameter ALMOST_EMPTY_OFFSET = FIFO_ITEMS/2;

    parameter ITEM_WIDTH = 32;

    parameter TRANSACTION_COUNT = 100000;

    parameter TX_CLK_PERIOD = 4ns;
    parameter RX_CLK_PERIOD = 5ns;

    parameter TX_RESET_CLKS = 10;
    parameter RX_RESET_CLKS = 10;

    `include "test.sv"

endpackage
`endif
