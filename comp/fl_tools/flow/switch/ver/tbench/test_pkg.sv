/*
 * test_pkg.sv: Test package
 * Copyright (C) 2009 CESNET
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

   import math_pkg::*; // log2()

   // Write debugging information
   `define DEBUG

   // Include Scoreboard
   `include "scoreboard.sv"

   // DUT GENERICS
   parameter DATA_WIDTH   = 16;
   parameter IF_COUNT     = 4;
   parameter IFNUM_OFFSET = 167;
   parameter PARTS        = 3;

   // TESTBENCH PARAMETERS
   parameter DREM_WIDTH   = log2(DATA_WIDTH/8);
   parameter FRAME_PARTS  = PARTS;

   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // TRANSACTION FORMAT
   parameter GENERATOR_FL_PACKET_COUNT      = FRAME_PARTS;   // pocet paketov vo frame
   int       GENERATOR_FL_PACKET_SIZE_MAX[] = '{10,512,32};   // maximalna velkost paketov
   int       GENERATOR_FL_PACKET_SIZE_MIN[] = '{5,64,1};      // minimalna velkost paketov

   // DRIVER0 PARAMETERS
   parameter DRIVER_DATA_WIDTH         = DATA_WIDTH;      // datova sirka driveru
   parameter DRIVER_DREM_WIDTH         = DREM_WIDTH;      // drem sirka driveru
   parameter DRIVER_DELAYEN_WT         = 1;                  // vaha delay enable medzi transakciami
   parameter DRIVER_DELAYDIS_WT        = 50;                  // vaha delay disable medzi transakciami
   parameter DRIVER_DELAYLOW           = 0;                  // spodna hranica delay medzi transakciami
   parameter DRIVER_DELAYHIGH          = 10;                  // horna hranica delay medzi transakciami
   parameter DRIVER_INSIDE_DELAYEN_WT  = 1;                  // vaha delay enable v transakcii
   parameter DRIVER_INSIDE_DELAYDIS_WT = 50;                  // vaha delay disable v transakcii
   parameter DRIVER_INSIDE_DELAYLOW    = 0;                  // spodna hranica delay v transakcii
   parameter DRIVER_INSIDE_DELAYHIGH   = 10;                  // horna hranica delay v transakcii

   // MONITOR PARAMETERS
   parameter MONITOR_DATA_WIDTH         = DATA_WIDTH;     // datova sirka monitoru
   parameter MONITOR_DREM_WIDTH         = DREM_WIDTH;     // drem sirka monitoru
   parameter MONITOR_DELAYEN_WT         = 1;                 // vaha delay enable medzi transakciami
   parameter MONITOR_DELAYDIS_WT        = 50;                 // vaha delay disable medzi transakciami
   parameter MONITOR_DELAYLOW           = 0;                 // spodna hranica delay medzi transakciami
   parameter MONITOR_DELAYHIGH          = 10;                 // horna hranica delay medzi transakciami
   parameter MONITOR_INSIDE_DELAYEN_WT  = 1;                 // vaha delay enable v transakcii
   parameter MONITOR_INSIDE_DELAYDIS_WT = 50;                 // vaha delay disable v transakcii
   parameter MONITOR_INSIDE_DELAYLOW    = 0;                 // spodna hranica delay v transakcii
   parameter MONITOR_INSIDE_DELAYHIGH   = 10;                 // horna hranica delay v transakcii


   // TEST PARAMETERS
   parameter TRANSACTION_COUNT = 30000; // Count of transactions to generate

endpackage
