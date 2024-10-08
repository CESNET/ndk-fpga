/*
 * test_pkg.sv: Test package
 * Copyright (C) 2010 CESNET
 * Author(s): Marek Santa <santa@liberouter.org>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Package declaration
// ----------------------------------------------------------------------------
package test_pkg;

   import math_pkg::*; // log2

   // -- DUT GENERICS --
    // FrameLink data width
   parameter DATA_WIDTH     = 64;
    // Number of channels, up to 64
   parameter CHANNELS       = 4;
    // Width of the STATUS signal for each flow, up to 16 bits
   parameter STATUS_WIDTH   = 10;
    // Width of counters, 16 to 64 bits
   parameter CNT_WIDTH      = 64;
    // Enable various counters
   parameter COUNT_DROP     = 1;
   parameter COUNT_PASS     = 1;
   parameter COUNT_DROP_LEN = 1;
   parameter COUNT_PASS_LEN = 1;
    // Generate output register on output FrameLink
    // (It's possible because on output FrameLink is not used st_rdy_n signal)
   parameter OUTPUT_REG     = 1;

   // -- TESTBENCH PARAMS --
   parameter DREM_WIDTH = log2(DATA_WIDTH/8); // drem width

   // -- CLOCKS AND RESETS --
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // -- TRANSACTION FORMAT --
   parameter GENERATOR0_FL_PACKET_COUNT      = 2;
   int       GENERATOR0_FL_PACKET_SIZE_MAX[] = '{64, 1526};
   int       GENERATOR0_FL_PACKET_SIZE_MIN[] = '{8, 64};

   // -- DRIVER0 PARAMETERS --
    // FL data width
   parameter DRIVER0_DATA_WIDTH         = DATA_WIDTH;
    // FL REM width
   parameter DRIVER0_DREM_WIDTH         = DREM_WIDTH;
    // Delay enable/disable between transactions weight
   parameter DRIVER0_DELAYEN_WT         = 0;
   parameter DRIVER0_DELAYDIS_WT        = 5;
    // Delay between transactions limits
   parameter DRIVER0_DELAYLOW           = 0;
   parameter DRIVER0_DELAYHIGH          = 10;
    // Delay enable/disalbe inside transaction weight
   parameter DRIVER0_INSIDE_DELAYEN_WT  = 0;
   parameter DRIVER0_INSIDE_DELAYDIS_WT = 5;
    // Delay inside transaction limits
   parameter DRIVER0_INSIDE_DELAYLOW    = 0;
   parameter DRIVER0_INSIDE_DELAYHIGH   = 10;

   // -- MONITOR0 PARAMETERS --
    // FL data width
   parameter MONITOR0_DATA_WIDTH         = DATA_WIDTH;
    // FL REM width
   parameter MONITOR0_DREM_WIDTH         = DREM_WIDTH;

   // -- MULTIPLEXOR PARAMETERS --
    // Delay between multiplexing limits
   parameter MULTIPLEXOR_MUXDELAYLOW     = 1;
   parameter MULTIPLEXOR_MUXDELAYHIGH    = 3;


   // -- TEST PARAMETERS --
    // Count of transactions to generate
   parameter TRANSACTION_COUNT = 2000;
    // Seed for RNG
   parameter RNG_SEED          = 7;

endpackage
