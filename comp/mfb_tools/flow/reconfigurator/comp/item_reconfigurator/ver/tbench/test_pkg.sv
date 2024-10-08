// test_pkg.sv: Test package
// Copyright (C) 2020 CESNET
// Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

package test_pkg;

    import math_pkg::*;

    parameter REGIONS        = 2;
    parameter REGION_SIZE    = 2;
    parameter RX_BLOCK_SIZE  = 8;
    parameter TX_BLOCK_SIZE  = 2;
    parameter RX_ITEM_WIDTH  = 8;
    parameter META_WIDTH     = 4+32; // The '+32' bits are used by the verification to pass original transaction length

    parameter META_MODE      = 0;
    parameter DEVICE         = "ULTRASCALE";

    parameter FRAME_SIZE_MIN    = 1;
    parameter FRAME_SIZE_MAX    = 8*REGIONS*REGION_SIZE*RX_BLOCK_SIZE;
    parameter TRANSACTION_COUNT = 1000;

    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

    parameter TX_ITEM_WIDTH = RX_ITEM_WIDTH*RX_BLOCK_SIZE/TX_BLOCK_SIZE;

endpackage

