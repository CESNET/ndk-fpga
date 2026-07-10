/*!
 * \file test_pkg.sv
 * \brief Test Package
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2026
 */
 /*
 * Copyright (C) 2026 CESNET z. s. p. o.
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

   parameter EXTRACTED_ITEMS  = 1;

   // Minimum frame size is one region (user constraint).
   parameter FRAME_SIZE_MIN = REGION_SIZE*BLOCK_SIZE;
   parameter FRAME_SIZE_MAX = 4000;
   parameter TRANSACTION_COUNT = 10000;

   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   `include "scoreboard.sv"

endpackage
