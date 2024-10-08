/* test_pkg.sv: test package
 * Copyright (C) 2024 BrnoLogic, Ltd.
 * Author(s): Radek Hajek <hajek@brnologic.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

package test_pkg;

    import math_pkg::*;

    parameter REGIONS     = 4;
    parameter REGION_SIZE = 8;
    parameter BLOCK_SIZE  = 8;
    parameter ITEM_WIDTH  = 8;
    parameter META_WIDTH  = 0;
    parameter USE_IN_PIPE  = 0;
    parameter USE_OUT_PIPE = 0;
    parameter AXI_DATA_WIDTH = REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
    parameter PIPE_TYPE = "SHREG";
    parameter DEVICE    = "7SERIES";

    `include "scoreboard.sv"
    `include "speed_meas.sv"

    parameter FRAME_SIZE_MAX    = 1025;
    parameter FRAME_SIZE_MIN    = 1;
    parameter TRANSACTION_COUNT = 100000;

    // enables speed meassurement
    parameter ENABLE_SPEED_TEST = 0;

    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

endpackage
