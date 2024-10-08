// test_pkg.sv: Test package
// Copyright (C) 2020 CESNET z. s. p. o.
// Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

package test_pkg;

    import math_pkg::*;
    import sv_common_pkg::*; // SystemVerilog Boolean

    parameter DATA_WIDTH         = 8;
    parameter ITEMS              = 64;
    parameter ADDR_WIDTH         = log2(ITEMS);
    parameter RESOURCES_SAVING   = 0;
    parameter WRITE_BEFORE_MATCH = TRUE;
    parameter READ_FROM_TCAM     = TRUE;
    parameter OUTPUT_READ_REGS   = TRUE;
    parameter USE_FRAGMENTED_MEM = FALSE;
    parameter DEVICE             = "ULTRASCALE";

    parameter WRITE_COUNT = 200;
    parameter MATCH_COUNT = 100000;
    parameter READ_COUNT  = 200;

    parameter FULL_PRINT = FALSE;

    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

    `include "scoreboard.sv"

endpackage
