/*!
 * \file test_pkg.sv
 * \brief Test Package
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */



package test_pkg;

    import math_pkg::*;
    `include "scoreboard.sv"


    // DUT GENERICS
    parameter DATA_WIDTH    = 512;
    parameter SOP_POS_WIDTH = 3;
    parameter ITEMS         = 2048;
    parameter EOP_POS_WIDTH = log2(DATA_WIDTH/8);

    parameter TOTAL_WIDTH = DATA_WIDTH + SOP_POS_WIDTH + EOP_POS_WIDTH + 1 + 1 + 1 + 1;

endpackage
