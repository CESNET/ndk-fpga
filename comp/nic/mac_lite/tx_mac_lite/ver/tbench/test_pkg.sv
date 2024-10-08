// test_pkg.sv
// Copyright (C) 2019 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

package test_pkg;

    import math_pkg::*;

    // TX MFB configuration, allows you to set the required output data width
    // according to the selected Ethernet standard.
    parameter TX_REGIONS      = 2;
    parameter TX_REGION_SIZE  = 8;
    parameter TX_BLOCK_SIZE   = 8;
    parameter TX_ITEM_WIDTH   = 8;

    // RX MFB configuration, by default the same as TX. Useful, for example,
    // for narrowing data width from 512b (RX) to 128b (TX).
    parameter RX_REGIONS      = TX_REGIONS;
    parameter RX_REGION_SIZE  = TX_REGION_SIZE;
    parameter RX_BLOCK_SIZE   = TX_BLOCK_SIZE;
    parameter RX_ITEM_WIDTH   = TX_ITEM_WIDTH;

    parameter RX_INCLUDE_CRC  = 0;
    parameter RX_INCLUDE_IPG  = 0;
    parameter CRC_INSERT_EN   = 0;
    parameter IPG_GENERATE_EN = 0;

    parameter FRAME_SIZE_MAX = 512;
    parameter FRAME_SIZE_MIN = 50;
    parameter TRANSACTION_COUNT = 4000;

    parameter RX_CLK_PERIOD = 5ns;
    parameter TX_CLK_PERIOD = 4ns;
    parameter MI_CLK_PERIOD = 7ns;
    parameter RESET_TIME = 10*MI_CLK_PERIOD;

    parameter VERBOSITY = 0;

    `include "scoreboard.sv"

endpackage
