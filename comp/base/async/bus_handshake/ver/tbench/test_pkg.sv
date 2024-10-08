// test_pkg.sv
// Copyright (C) 2020 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

package test_pkg;

    import math_pkg::*;
    `include "scoreboard.sv"

    parameter DATA_WIDTH = 32;

    parameter TRANSACTION_COUNT = 100000;

    parameter RX_CLK_PERIOD = 5ns;
    parameter TX_CLK_PERIOD = 3ns;
    parameter RESET_TIME = 10*RX_CLK_PERIOD;

endpackage
