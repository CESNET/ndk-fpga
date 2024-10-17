// test_pkg.sv: Test package
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Tomas Fukac <fukac@cesnet.cz>
//            Tomas Hak <hak@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

package test_pkg;

    import math_pkg::*;
    import sv_common_pkg::*; // SystemVerilog Boolean

    parameter MVB_ITEMS          = 4;
    parameter REPLICAS           = MVB_ITEMS;
    parameter DATA_WIDTH         = 8;
    parameter ITEMS              = 64;
    parameter RESOURCES_SAVING   = 0;
    parameter WRITE_BEFORE_MATCH = TRUE;
    parameter READ_FROM_TCAM     = TRUE;
    parameter OUTPUT_READ_REGS   = TRUE;
    parameter USE_FRAGMENTED_MEM = FALSE;
    parameter DEVICE             = "ULTRASCALE";

    parameter IS_INTEL           = (DEVICE == "AGILEX" || DEVICE == "STRATIX10" || DEVICE == "ARRIA10");
    // with USE_FRAGMENTED_MEM = TRUE, ITEMS must be aligned to multiples of 20 for Intel FPGAs
    parameter MLAB_ITEMS         = USE_FRAGMENTED_MEM ? 20 : 16;
    parameter SLICEM_ITEMS       = DEVICE == "ULTRASCALE" ? (USE_FRAGMENTED_MEM ? 14 : 8) : (USE_FRAGMENTED_MEM ? 6 : 4);
    parameter BLOCK_ITEMS        = IS_INTEL ? MLAB_ITEMS : SLICEM_ITEMS;
    parameter ITEMS_ALIGNED      = USE_FRAGMENTED_MEM ? (ITEMS/BLOCK_ITEMS)*(2**log2(BLOCK_ITEMS)) : ITEMS;
    parameter ADDR_WIDTH         = log2(ITEMS_ALIGNED);

    parameter WRITE_COUNT = 200;
    parameter MATCH_COUNT = 100000;
    parameter READ_COUNT  = 200;

    parameter FULL_PRINT = FALSE;

    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

    `include "../../../../../base/mem/tcam2/ver/tbench/scoreboard.sv"

endpackage
