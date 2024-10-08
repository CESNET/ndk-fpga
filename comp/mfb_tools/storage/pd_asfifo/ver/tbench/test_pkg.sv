/*!
 * \file test_pkg.sv
 * \brief Test Package
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2018
 */
 /*
 * Copyright (C) 2018 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

package test_pkg;

   import math_pkg::*;
   import sv_common_pkg::*; // SystemVerilog Boolean

   // FIFO depth in words
   parameter ITEMS = 512;

   // MFB bus parameters
   parameter REGIONS     = 4;
   parameter REGION_SIZE = 8;
   parameter BLOCK_SIZE  = 8;
   parameter ITEM_WIDTH  = 8;

   // MFB responder parameters
   parameter DST_RDY_DOWN_CHANCE   = 60; // [%]
   parameter DST_RDY_DOWN_TIME_MIN = 0;
   parameter DST_RDY_DOWN_TIME_MAX = 10;

   // MFB driver parameters
   parameter FRAME_SIZE_MAX    = 1024;
   parameter FRAME_SIZE_MIN    = 60;
   parameter TRANSACTION_COUNT = 10000;

   // FD driver parameters
   parameter FD_SRC_RDY_DOWN_CHANCE   = 95; // [%]
   parameter FD_SRC_RDY_DOWN_TIME_MIN = 20;
   parameter FD_SRC_RDY_DOWN_TIME_MAX = 55;

   // Test parameters
   parameter FULL_PRINT = FALSE;

   // Clock and reset parameters
   parameter RX_CLK_PERIOD = 8ns;
   parameter TX_CLK_PERIOD = 5ns;
   parameter RESET_TIME    = 50ns;

   `include "scoreboard.sv"

endpackage
