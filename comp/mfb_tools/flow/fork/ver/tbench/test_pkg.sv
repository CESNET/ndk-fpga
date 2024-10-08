/*!
 * \file test_pkg.sv
 * \brief Test Package
 * \author Daniel Kříž <xkrizd01@vutbr.cz>
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

    parameter OUTPUT_PORTS = 2;

    parameter REGIONS      = 4;
    parameter REGION_SIZE  = 8;
    parameter BLOCK_SIZE   = 8;
    parameter ITEM_WIDTH   = 8;
    parameter META_WIDTH   = 8;
    parameter USE_DST_RDY  = 1;
    parameter VERSION      = "logic";

    parameter VERBOSE      = 0;

    parameter FRAME_SIZE_MAX    = 512;
    parameter FRAME_SIZE_MIN    = 32;
    parameter TRANSACTION_COUNT = 1000;

    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

    `include "scoreboard.sv"

endpackage
