/*!
 * \file test_pkg.sv
 * \brief Test Package
 * \author Daniel Kondys <xkondy00@vutbr.cz>
 * \date 2019
 */
 /*
 * Copyright (C) 2019 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */



package test_pkg;

    import math_pkg::*;


    parameter REGIONS = 2;
    parameter REGION_SIZE = 1;
    parameter BLOCK_SIZE = 8;
    parameter ITEM_WIDTH = 32;


    parameter FRAME_SIZE_MAX = 512;
    parameter FRAME_SIZE_MIN = 60;
    parameter TRANSACTION_COUNT = 50000;


    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10*CLK_PERIOD;
    `include "scoreboard.sv"

endpackage
