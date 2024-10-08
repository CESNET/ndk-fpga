// test_pkg.sv : Test Package
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Vladislav Valek <valekv@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-CLause

package test_pkg;

    import math_pkg::*;
    `include "scoreboard.sv"

    parameter REGIONS     = 1;
    parameter REGION_SIZE = 4;
    parameter BLOCK_SIZE  = 8;
    parameter ITEM_WIDTH  = 8;


    parameter FRAME_SIZE_MAX    = 512;
    parameter FRAME_SIZE_MIN    = 60;
    parameter TRANSACTION_COUNT = 100000;

    parameter CLK_PERIOD = 4ns;
    parameter RESET_TIME = 20*CLK_PERIOD;

endpackage
