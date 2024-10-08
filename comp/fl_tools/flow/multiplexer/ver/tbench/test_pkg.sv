/*
 * test_pkg.sv: FL_MULTIPLEXER Test package
 * Copyright (C) 2010 CESNET
 * Author(s): Marek Santa <santa@liberouter.org>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package test_pkg;

  import math_pkg::*; // log2()

  // standard SystemVerilog Scoreboard
  `include "scoreboard.sv"

  // -- FL_MULTIPLEXER GENERICS ----------------------------------------------
   // Number of Frame Link channels
  parameter CHANNELS       = 4;
   // Frame Link Data Width
  parameter DATA_WIDTH     = 64;
  parameter DREM_WIDTH     = log2(DATA_WIDTH/8);

   // CLOCKS AND RESETS
  parameter CLK_PERIOD = 10ns;
  parameter RESET_TIME = 10*CLK_PERIOD;

  // -- TRANSACTION FORMAT ---------------------------------------------------
   // Number of packets in one frame
  parameter GENERATOR_PACKET_COUNT      = 2;
   // Max size of packets
  int       GENERATOR_PACKET_SIZE_MAX[] = '{64,1536,128};
   // Min size of packets
  int       GENERATOR_PACKET_SIZE_MIN[] = '{8,32,8};

  // -- TEST PARAMETERS ------------------------------------------------------
   // Count of transactions to generate
  parameter TEST_TRANSACTION_COUNT     = 5000;

  // -- DRIVER PARAMETERS ---------------------------------------------------
   // FL data width
  parameter DRIVER_DATA_WIDTH         = DATA_WIDTH;
   // FL REM width
  parameter DRIVER_DREM_WIDTH         = DREM_WIDTH;
   // Delay enable/disable between transactions weight
  parameter DRIVER_DELAYEN_WT         = 1;
  parameter DRIVER_DELAYDIS_WT        = 10;
   // Delay between transactions limits
  parameter DRIVER_DELAYLOW           = 0;
  parameter DRIVER_DELAYHIGH          = 7;
   // Delay enable/disalbe inside transaction weight
  parameter DRIVER_INSIDE_DELAYEN_WT  = 1;
  parameter DRIVER_INSIDE_DELAYDIS_WT = 50;
   // Delay inside transaction limits
  parameter DRIVER_INSIDE_DELAYLOW    = 0;
  parameter DRIVER_INSIDE_DELAYHIGH   = 7;

  // -- MONITOR PARAMETERS --------------------------------------------------
   // FL data width
  parameter MONITOR_DATA_WIDTH         = DATA_WIDTH;
   // FL REM width
  parameter MONITOR_DREM_WIDTH         = DREM_WIDTH;
   // Delay enable/disable between transactions weight
  parameter MONITOR_DELAYEN_WT         = 1;
  parameter MONITOR_DELAYDIS_WT        = 10;
   // Delay between transactions limits
  parameter MONITOR_DELAYLOW           = 0;
  parameter MONITOR_DELAYHIGH          = 7;
   // Delay enable/disalbe inside transaction weight
  parameter MONITOR_INSIDE_DELAYEN_WT  = 1;
  parameter MONITOR_INSIDE_DELAYDIS_WT = 50;
   // Delay inside transaction limits
  parameter MONITOR_INSIDE_DELAYLOW    = 0;
  parameter MONITOR_INSIDE_DELAYHIGH   = 7;

endpackage
