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

    parameter FIFO_ITEMS = 128;
    parameter DATA_WIDTH = 32;

    parameter TRANSACTION_COUNT = 100000;

    parameter RX_CLK_PERIOD = 5ns;
    parameter TX_CLK_PERIOD = 4ns;
    parameter RESET_TIME = 10*RX_CLK_PERIOD;

endpackage
