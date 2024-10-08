/*!
 * \file test_pkg.sv
 * \brief Test Package
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2017
 */
 /*
 * Copyright (C) 2017 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

package test_pkg;

    import math_pkg::*;
    `include "scoreboard.sv"

    parameter FRAME_SIZE_MAX    = 1500;
    parameter FRAME_SIZE_MIN    = 60;
    parameter TRANSACTION_COUNT = 10000;

    parameter FLU_CLK_PERIOD  = 5ns;
    parameter CMAC_CLK_PERIOD = 3.1ns;
    parameter MI_CLK_PERIOD   = 5ns;
    parameter RESET_TIME      = 10*FLU_CLK_PERIOD;

endpackage
