/*!
 * \file test_pkg.sv
 * \brief Test Package
 * \author Daniel Kriz <xkrizd01@vutbr.cz>
 * \date 2020
 */
 /*
 * Copyright (C) 2020 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

package test_pkg;

    import math_pkg::*;

    parameter REGIONS        = 1;
    parameter REGION_SIZE    = 8;
    parameter BLOCK_SIZE     = 8;
    parameter ITEM_WIDTH     = 8;

    parameter OUTPUT_REG     = 1;
    parameter CNT_WIDTH      = 32;
    parameter AUTO_RESET     = 1;
    parameter IMPLEMENTATION = "parallel";

    parameter longint CNT_WIDTH_MAX = 2**CNT_WIDTH;
    parameter FRAME_SIZE_MAX        = 512;
    parameter FRAME_SIZE_MIN        = 60;
    parameter TRANSACTION_COUNT     = 2000;

    parameter VERBOSE = 0;

    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

    `include "scoreboard.sv"
endpackage
