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

    parameter OUTPUT_PORTS = 2;

    parameter ITEMS        = 4;
    parameter ITEM_WIDTH   = 8;
    parameter USE_DST_RDY  = 1;
    parameter VERSION      = "logic";

    parameter VERBOSE      = 0;

    parameter TRANSACTION_COUNT = 2000;

    parameter CLK_PERIOD = 10ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

    `include "scoreboard.sv"

endpackage
