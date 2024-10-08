/*!
 * \file test_pkg.sv
 * \brief Test Package
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2018
 */
 /*
 * Copyright (C) 2018 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

package test_pkg;

    import math_pkg::*;
    import sv_common_pkg::*; // SystemVerilog Boolean

    parameter MVB_ITEMS       = 2;
    parameter MFB_REGIONS     = 4;
    parameter MFB_REGION_SIZE = 1;
    parameter MFB_BLOCK_SIZE  = 4;
    parameter MFB_ITEM_WIDTH  = 32;

    parameter MFB_REG_WIDTH   = 128; // MFB_REG_WIDTH = MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH
    parameter INPUT_FIFO_SIZE = 2;
    parameter DMA_DOWNHDR_WIDTH = 32;

   // Generator parameters
   parameter FRAME_SIZE_MAX = 500; // size is in MFB items
   parameter FRAME_SIZE_MIN = 1; // size is in MFB items
   parameter TRANSACTION_COUNT = 10000;

   // Test parameters
   parameter FULL_PRINT = FALSE;

   // Clock and reset parameters
   parameter CLK_PERIOD = 5ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   `include "scoreboard.sv"
   `include "custom_gen.sv"

endpackage
