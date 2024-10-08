// test_pkg.sv
// Copyright (C) 2020 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

package test_pkg;

    import math_pkg::*;

    // MII configuration, allows you to set the required output data width
    // according to the selected Ethernet standard.
    parameter MII_DATA_WIDTH  = 1024;
    parameter MIIA_LANE_WIDTH = (MII_DATA_WIDTH==64) ? 32 : 64; //calculated automatically
    parameter MII_LANE_WIDTH  = MIIA_LANE_WIDTH;

    parameter RX_INCLUDE_CRC  = 0;
    parameter RX_INCLUDE_IPG  = 0;

    parameter FRAME_SIZE_MAX = 512;
    parameter FRAME_SIZE_MIN = 50;
    parameter TRANSACTION_COUNT = 20000;

    parameter RX_CLK_PERIOD = 5ns;
    parameter TX_CLK_PERIOD = 4ns;
    parameter MI_CLK_PERIOD = 7ns;
    parameter RESET_TIME = 10*MI_CLK_PERIOD;

    // By default the (RX-AUTO) parameters are calculated automatically from MII_DATA_WIDTH.
    parameter RXA_REGIONS     = math_pkg::max(MII_DATA_WIDTH/512,1);
    parameter RXA_BLOCK_SIZE  = 8;
    parameter RXA_ITEM_WIDTH  = 8;
    parameter RXA_REGION_SIZE = (MII_DATA_WIDTH/RXA_REGIONS)/(RXA_BLOCK_SIZE*RXA_ITEM_WIDTH);

    // By default the (RX) parameters are calculated automatically from MII_DATA_WIDTH.
    // Useful for narrowing data width from 512b (RX) to 64b (MII).
    parameter RX_REGIONS     = RXA_REGIONS;
    parameter RX_BLOCK_SIZE  = RXA_BLOCK_SIZE;
    parameter RX_ITEM_WIDTH  = RXA_ITEM_WIDTH;
    parameter RX_REGION_SIZE = RXA_REGION_SIZE;

    `include "scoreboard.sv"

endpackage
