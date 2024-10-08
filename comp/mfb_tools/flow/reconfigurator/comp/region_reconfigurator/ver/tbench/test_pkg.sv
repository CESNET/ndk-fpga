// test_pkg.sv: Test package
// Copyright (C) 2020 CESNET
// Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

package test_pkg;

    import math_pkg::*;
    `include "scoreboard.sv"

    parameter RX_REGIONS     = 8;
    parameter TX_REGIONS     = 2;
    parameter RX_REGION_SIZE = 4;
    parameter BLOCK_SIZE     = 2;
    parameter ITEM_WIDTH     = 4;
    parameter META_WIDTH     = 4;

    parameter META_MODE   = 0; // 0 - SOF, 1 - EOF

    parameter FIFO_SIZE   = 32;
    parameter DEVICE      = "ULTRASCALE";

    parameter FRAME_SIZE_MIN    = 1;
    parameter FRAME_SIZE_MAX    = 8*RX_REGIONS*RX_REGION_SIZE*BLOCK_SIZE;
    parameter TRANSACTION_COUNT = 1000;

    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

endpackage

