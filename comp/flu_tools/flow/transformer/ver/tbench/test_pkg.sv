/*
 * test_pkg.sv: Test package
 * Copyright (C) 2013 CESNET
 * Author: Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package test_pkg;

   // Include this file if you want to use standard SystemVerilog Scoreboard
   `include "scoreboard.sv"

   // DUT GENERICS
   parameter RX_DATA_WIDTH    = 512;        // RX Data width
   parameter RX_SOP_POS_WIDTH = 3;
   parameter TX_DATA_WIDTH    = 64;        // TX Data width
   parameter TX_SOP_POS_WIDTH = 0;

   parameter RX_EOP_POS_WIDTH = $clog2(RX_DATA_WIDTH/8);     // RX Data Reminder width
   parameter TX_EOP_POS_WIDTH = $clog2(TX_DATA_WIDTH/8);     // TX Data Reminder width
   parameter RX_SOP_POS_WIDTH_FIX = math_pkg::max(1,RX_SOP_POS_WIDTH);
   parameter TX_SOP_POS_WIDTH_FIX = math_pkg::max(1,TX_SOP_POS_WIDTH);

   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // TRANSACTION FORMAT
   int       GENERATOR_FLU_PACKET_SIZE_MAX = 512;
   int       GENERATOR_FLU_PACKET_SIZE_MIN = 64;

   // DRIVER PARAMETERS
   parameter DRIVER_INSIDE_DELAYEN_WT  = 1;
   parameter DRIVER_INSIDE_DELAYDIS_WT = 5;
   parameter DRIVER_INSIDE_DELAYLOW    = 0;
   parameter DRIVER_INSIDE_DELAYHIGH   = 5;
   parameter DRIVER_START_POS_LOW      = 0;
   parameter DRIVER_START_POS_HIGH     = 2**RX_SOP_POS_WIDTH-1;

   // MONITOR PARAMETERS
   parameter MONITOR_DELAYEN_WT  = 1;
   parameter MONITOR_DELAYDIS_WT = 5;
   parameter MONITOR_DELAYLOW    = 0;
   parameter MONITOR_DELAYHIGH   = 5;
   parameter MONITOR_INSIDE_DELAYEN_WT  = 1;
   parameter MONITOR_INSIDE_DELAYDIS_WT = 5;
   parameter MONITOR_INSIDE_DELAYLOW    = 0;
   parameter MONITOR_INSIDE_DELAYHIGH   = 5;


   // TEST PARAMETERS
   parameter TRANSACTION_COUNT = 10000;

endpackage
