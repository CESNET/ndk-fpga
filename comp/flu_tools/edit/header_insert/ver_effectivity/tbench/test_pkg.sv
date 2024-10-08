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

   import math_pkg::*;       // log2()

   // Include this file if you want to use standard SystemVerilog Scoreboard
   `include "scoreboard.sv"

   // DUT GENERICS
   parameter DATA_WIDTH    = 512;        // RX Data width
   parameter SOP_POS_WIDTH = 3;
   parameter HDR_WIDTH    = 128;        // TX Data width

   parameter EOP_POS_WIDTH = log2(DATA_WIDTH/8);     // RX Data Reminder width
   parameter HDR_POS_WIDTH = log2(HDR_WIDTH/8);

   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // TRANSACTION FORMAT
   int       GENERATOR_FLU_PACKET_SIZE_MAX = 252;
   int       GENERATOR_FLU_PACKET_SIZE_MIN = 60;

   // DRIVER PARAMETERS
   parameter DRIVER_INSIDE_DELAYEN_WT  = 0;
   parameter DRIVER_INSIDE_DELAYDIS_WT = 5;
   parameter DRIVER_INSIDE_DELAYLOW    = 0;
   parameter DRIVER_INSIDE_DELAYHIGH   = 5;
   parameter DRIVER_START_POS_LOW      = 0;
   parameter DRIVER_START_POS_HIGH     = 2**SOP_POS_WIDTH-1;

   parameter HDRIVER_INSIDE_DELAYEN_WT  = 0;
   parameter HDRIVER_INSIDE_DELAYDIS_WT = 5;
   parameter HDRIVER_INSIDE_DELAYLOW    = 0;
   parameter HDRIVER_INSIDE_DELAYHIGH   = 5;

   // MONITOR PARAMETERS
   parameter MONITOR_DELAYEN_WT  = 0;
   parameter MONITOR_DELAYDIS_WT = 5;
   parameter MONITOR_DELAYLOW    = 0;
   parameter MONITOR_DELAYHIGH   = 5;
   parameter MONITOR_INSIDE_DELAYEN_WT  = 0;
   parameter MONITOR_INSIDE_DELAYDIS_WT = 5;
   parameter MONITOR_INSIDE_DELAYLOW    = 0;
   parameter MONITOR_INSIDE_DELAYHIGH   = 5;


   // TEST PARAMETERS
   parameter TRANSACTION_COUNT = 10000;

endpackage
