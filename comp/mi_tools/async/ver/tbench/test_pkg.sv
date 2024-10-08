/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package test_pkg;

   import math_pkg::*;//log2

   // CLOCKS AND RESETS
   parameter MASTER_CLK_PERIOD = 8ns;
   parameter SLAVE_CLK_PERIOD  = 6.25ns;
   parameter RESET_TIME        = 10*MASTER_CLK_PERIOD;

   // -------- TEST PARAMETERS -----------------------------------------------
    // Count of transactions to generate
   parameter TRANSACTION_COUNT = 400000;

   ///////////////////////
   // MI SETTINGS
   parameter MI_WIDTH = 32;
   parameter MI_META_WIDTH = 2;
endpackage
