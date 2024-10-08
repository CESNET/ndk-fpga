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
   parameter CLK_PERIOD = 5ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // -------- TEST PARAMETERS -----------------------------------------------
    // Count of transactions to generate
   parameter TRANSACTION_COUNT = 20000;

   ///////////////////////
   // MI SETTINGS
   parameter RX_DATA_WIDTH = 32;
   parameter TX_DATA_WIDTH = 32;

   parameter ADDR_WIDTH = 32;
   parameter META_WIDTH = 16;

   parameter VERBOSITY = 0;

   `include "scoreboard.sv"

endpackage
