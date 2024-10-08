// test_pkg.sv: Test package
// Copyright (C) 2020 CESNET
// Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

package test_pkg;

    import math_pkg::*;
    `include "scoreboard.sv"

    parameter REGIONS        = 2;
    parameter RX_REGION_SIZE = 8;
    parameter TX_REGION_SIZE = 2;
    parameter RX_BLOCK_SIZE  = 8;
    parameter ITEM_WIDTH     = 4;
    parameter META_WIDTH     = 4;

    parameter META_MODE      = 0; // 0 - SOF, 1 - EOF

    parameter FIFO_SIZE      = 16;
    parameter FRAME_ALIGN    = 0;
    parameter DEVICE         = "ULTRASCALE";

    parameter FRAME_SIZE_MIN    = 1;
    parameter FRAME_SIZE_MAX    = 8*REGIONS*RX_REGION_SIZE*RX_BLOCK_SIZE;
    parameter TRANSACTION_COUNT = 1000;

    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

endpackage

