// pkg.sv: Test package
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Vladislav Valek <xvalek14@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


`ifndef MFB_TO_LBUS_ADAPTER_TEST_SV
`define MFB_TO_LBUS_ADAPTER_TEST_SV

package test;

    `include "uvm_macros.svh"
    import uvm_pkg::*;

    parameter RX_REGIONS         = 1;
    parameter RX_REGION_SIZE     = 8;
    parameter RX_BLOCK_SIZE      = 8;
    parameter RX_ITEM_WIDTH      = 8;

    parameter TX_REGIONS         = 1;
    parameter TX_REGION_SIZE     = 4;
    parameter TX_BLOCK_SIZE      = 16;
    parameter TX_ITEM_WIDTH      = 8;

    parameter DRAIN_TIME         = 20ns;
    parameter TRANSACTION_COUNT  = 1000000;

    parameter CLK_PERIOD         = 2500ps;

    parameter RESET_CLKS         = 10;

    `include "sequence.sv"
    `include "test.sv"
endpackage
`endif
