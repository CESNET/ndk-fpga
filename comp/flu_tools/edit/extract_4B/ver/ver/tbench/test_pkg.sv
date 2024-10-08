/*
 * test_pkg.sv: Test package
 * Copyright (C) 2015 CESNET
 * Author: Pavel Benacek <benacek@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

`include "flue_ifc.sv"

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package test_pkg;

   import math_pkg::*;       // log2()

   // Include this file if you want to use standard SystemVerilog Scoreboard
   `include "flue_transaction.sv"
   `include "flue_driver.sv"
   `include "scoreboard.sv"

   // DUT GENERICS
   parameter DATA_WIDTH    = 512;        // RX Data width
   parameter SOP_POS_WIDTH = 3;
   parameter EOP_POS_WIDTH = log2(DATA_WIDTH/8);     // RX Data Reminder width
   parameter OFFSET_WIDTH  = 10;
   parameter INPUT_PIPE    = TRUE;

   parameter TX_DATA_WIDTH    = 32;        // RX Data width
   parameter TX_SOP_POS_WIDTH = 1;
   parameter TX_EOP_POS_WIDTH = log2(TX_DATA_WIDTH/8);     // RX Data Reminder width

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
   parameter DRIVER_START_POS_HIGH     = 2**SOP_POS_WIDTH-1;

   parameter HDRIVER_INSIDE_DELAYEN_WT  = 1;
   parameter HDRIVER_INSIDE_DELAYDIS_WT = 5;
   parameter HDRIVER_INSIDE_DELAYLOW    = 0;
   parameter HDRIVER_INSIDE_DELAYHIGH   = 5;

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
   parameter TRANSACTION_COUNT = 100000;

endpackage : test_pkg
