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


    parameter ITEMS = 4;
    parameter ITEM_WIDTH = 8;
    parameter FAKE_PIPE = 0;
    parameter USE_DST_RDY = 1;


    parameter TRANSACTION_COUNT = 10000;


    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

endpackage
