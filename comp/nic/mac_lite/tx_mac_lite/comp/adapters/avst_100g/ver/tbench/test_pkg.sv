/*!
 * \file test_pkg.sv
 * \brief Test Package
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2017
 */
 /*
 * Copyright (C) 2017 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

package test_pkg;

    import math_pkg::*;
    `include "scoreboard.sv"

    parameter DATA_WIDTH = 512;
    parameter BLOCK_SIZE = DATA_WIDTH/64;
    parameter FIFO_DEPTH = 2048;

    parameter FRAME_SIZE_MAX    = 5120;
    parameter FRAME_SIZE_MIN    = 60;
    parameter TRANSACTION_COUNT = 20000;

    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

endpackage
