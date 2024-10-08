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

    parameter RX0_ITEMS      = 4;
    parameter RX0_ITEM_WIDTH = 32;
    parameter RX1_ITEMS      = 3;
    parameter RX1_ITEM_WIDTH = 16;

    parameter VERBOSE    = 0;

    parameter TRANSACTION_COUNT = 20000;

    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

    `include "scoreboard.sv"

endpackage
