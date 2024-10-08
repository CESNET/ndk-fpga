/*!
 * \file test_pkg.sv
 * \brief Test Package
 * \author Jakub Cabal <xcabal05@stud.feec.vutbr.cz>
 * \date 2017
 */
 /*
 * Copyright (C) 2017 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */



package test_pkg;

    import math_pkg::*;
    `include "scoreboard.sv"

    parameter REGIONS = 2;
    parameter REGION_SIZE = 1;
    parameter BLOCK_SIZE = 8;
    parameter ITEM_WIDTH = 32;

    parameter FRAME_SIZE_MAX = 512;
    parameter FRAME_SIZE_MIN = 60;
    parameter TRANSACTION_COUNT = 10000;

    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

endpackage
