// test_pkg.sv: Test package
// Copyright (C) 2020 CESNET
// Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

package test_pkg;

    import math_pkg::*;
    `include "scoreboard.sv"


    parameter RX_REGIONS = 2;
    parameter TX_REGIONS = 1;
    parameter REGION_SIZE = 1;
    parameter BLOCK_SIZE = 8;
    parameter ITEM_WIDTH = 32;


    parameter FRAME_SIZE_MAX = 512;
    parameter FRAME_SIZE_MIN = 60;
    parameter TRANSACTION_COUNT = 100000;


    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

endpackage

