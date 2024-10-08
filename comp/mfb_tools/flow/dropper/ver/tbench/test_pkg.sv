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

   parameter REGIONS      = 4;
   parameter REGION_SIZE  = 8;
   parameter BLOCK_SIZE   = 8;
   parameter ITEM_WIDTH   = 8;

   parameter FRAME_SIZE_MAX = 1024;
   parameter FRAME_SIZE_MIN = 1;
   parameter TRANSACTION_COUNT = 50000;

   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   `include "scoreboard.sv"

endpackage
