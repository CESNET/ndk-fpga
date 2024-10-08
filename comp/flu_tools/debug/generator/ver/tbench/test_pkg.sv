/*
 * test_pkg.sv: Test package with verification parameters
 * Copyright (C) 2018 CESNET
 * Author(s): Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

package test_pkg;
    import math_pkg::*;
    `include "scoreboard.sv"

    parameter DATA_WIDTH = 512;
    parameter SOP_POS_WIDTH = 3;
    parameter EOP_POS_WIDTH = log2(DATA_WIDTH/8);

    parameter CLK_PERIOD = 5ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

    //int       LENGTHS[] = '{60, 100, 116, 140};
    parameter GENERATOR_WAIT = 10000;
    parameter IDLE_WAIT = 100;
endpackage
