// file test_pkg.sv: Test Package
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kondys <xkondy00@vutbr.cz>
//
// SPDX-License-Identifier: BSD-3-Clause


package test_pkg;

    import math_pkg::*;

    parameter REGIONS     = 1;
    parameter REGION_SIZE = 1;
    parameter BLOCK_SIZE  = 64;
    parameter ITEM_WIDTH  = 8;
    parameter META_WIDTH  = 1;

    parameter DATA_WIDTH     = 512;
    parameter TX_REGIONS     = 1;
    parameter TX_REGION_SIZE = 8;
    parameter TX_BLOCK_SIZE  = 8;
    parameter TX_ITEM_WIDTH  = 8;

    parameter FRAME_SIZE_MIN    = 8;
    parameter FRAME_SIZE_MAX    = 128;
    parameter TRANSACTION_COUNT = 50000;

    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

    `include "scoreboard.sv"
endpackage
