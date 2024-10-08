// test_pkg.sv
// Copyright (C) 2020 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

package test_pkg;

    import math_pkg::*;

    parameter DEVICE = "ULTRASCALE";

    parameter MFB_REGIONS     = 4;
    parameter MFB_REGION_SIZE = 8;
    parameter MFB_BLOCK_SIZE  = 8;
    parameter MFB_ITEM_WIDTH  = 8;

    parameter LENGTH_WIDTH   = 16;
    parameter CHANNELS_WIDTH = 4;
    parameter PKT_CNT_WIDTH  = 64;
    parameter USE_PACP_ARCH  = 1'b0;

    parameter CLK_PERIOD = 5ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

    // DO NOT CHANGE
    parameter MFB_META_WIDTH = MFB_REGIONS*(CHANNELS_WIDTH+LENGTH_WIDTH);

    `include "scoreboard.sv"

endpackage
