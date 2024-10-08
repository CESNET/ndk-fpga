/*!
 * \file test_pkg.sv
 * \brief Test Package
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */



package test_pkg;

    import math_pkg::*;
    `include "scoreboard.sv"


    parameter DEVICE = "ULTRASCALE";
    parameter REGIONS = 4;
    parameter REGION_SIZE = 8;
    parameter BLOCK_SIZE = 8;
    parameter ITEM_WIDTH = 8;
    parameter ITEMS = 1024;


    parameter FRAME_SIZE_MAX = 512;
    parameter FRAME_SIZE_MIN = 60;
    parameter TRANSACTION_COUNT = 10000;


    parameter RX_CLK_PERIOD = 5ns;
    parameter TX_CLK_PERIOD = 6ns;
    parameter RESET_TIME = 10*RX_CLK_PERIOD;

endpackage
