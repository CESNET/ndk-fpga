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

   parameter REGIONS     = 2; // any power of two
   parameter REGION_SIZE = 8; // any power of two
   parameter BLOCK_SIZE  = 8; // any power of two
   parameter ITEM_WIDTH  = 8; // any positive
   parameter LEN_WIDTH   = 8;

   // Generator parameters
   parameter TRANSACTION_COUNT = 100000;

   // Clock and reset parameters
   parameter CLK_PERIOD  = 5ns;
   parameter RESET_TIME  = 10*CLK_PERIOD;

   `include "scoreboard.sv"

endpackage
