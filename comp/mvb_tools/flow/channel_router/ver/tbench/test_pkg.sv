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


    parameter ITEMS = 8;
    parameter ITEM_WIDTH = 77;
    parameter SRC_CHANNELS = 16;
    parameter DST_CHANNELS = 32;
    parameter MI_DATA_WIDTH = 32;
    parameter MI_ADDR_WIDTH = 32;
    parameter OPT_MODE = 0;
    parameter DEVICE = "ULTRASCALE";

    parameter NEW_RX_ITEM_WIDTH = ITEM_WIDTH+math_pkg::log2(SRC_CHANNELS);
    parameter NEW_TX_ITEM_WIDTH = ITEM_WIDTH+math_pkg::log2(DST_CHANNELS);
    parameter TRANSACTION_COUNT = 1000;
    // VERBOSE = 1 show transaction
    // VERBOSE = 2 show IN adn OUT channel
    // VERBOSE = 3 show values of counters
    // VERBOSE = 4 show information about register
    parameter VERBOSE = 0;
    // REG_SETTINGS = 0 set default settings
    // REG_SETTINGS = 1 set increment to SRC_CHANNELS and then at 1
    // REG_SETTINGS = 2 set some random combinations
    // REG_SETTINGS = 3 increment = (i+1)*i, min channel = i and max channel = i+32-1
    parameter REG_SETTINGS = 1;


    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

    `include "scoreboard.sv"

endpackage
