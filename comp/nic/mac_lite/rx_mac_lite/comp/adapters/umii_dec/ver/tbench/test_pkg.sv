// test_pkg.sv
// Copyright (C) 2019 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

package test_pkg;

    import math_pkg::*;

    // DUT parameters
    parameter MII_DATA_WIDTH = 2048;
    parameter MII_LANE_WIDTH = (MII_DATA_WIDTH==64) ? 32 : 64;

    // Generator parameters
    int FRAME_SIZE_MAX[]        = '{1520,256};
    int FRAME_SIZE_MIN[]        = '{60,1};
    int TRANSACTION_CHECK[]     = '{1,0};
    parameter TRANSACTION_COUNT = 50000;

    // Timing parameters
    parameter CLK_PERIOD = 5.12ns;
    parameter RESET_TIME = 10*CLK_PERIOD;

    // MFB parameters - WARNING: The MFB parameters are calculated automatically,
    // they cannot be changed manually!!!
    parameter REGIONS     = math_pkg::max(MII_DATA_WIDTH/512,1);
    parameter BLOCK_SIZE  = 8;
    parameter ITEM_WIDTH  = 8;
    parameter REGION_SIZE = (MII_DATA_WIDTH/REGIONS)/(BLOCK_SIZE*ITEM_WIDTH);

endpackage
