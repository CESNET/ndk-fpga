/*
 * test_pkg.sv: FL_BINDER Test package
 * Copyright (C) 2008 CESNET
 * Author(s): Martin Kosek <kosek@liberouter.org>
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

  // FL_BINDER GENERICS
  parameter INPUT_COUNT       = 2;
  parameter INPUT_WIDTH       = 64;
  parameter INPUT_DREM_WIDTH  = log2(INPUT_WIDTH/8);
  parameter OUTPUT_WIDTH      = 64;
  parameter OUTPUT_DREM_WIDTH = log2(OUTPUT_WIDTH/8);
  parameter FRAME_PARTS       = 3;

  parameter LUT_MEMORY        = 0;
  parameter LUT_BLOCK_SIZE    = 16;       // INPUT_WIDTH*INPUT_COUNT wide
  parameter SIMPLE_BINDER     = 0;
  parameter STUPID_BINDER     = 0;

  // CLOCKS AND RESETS
  parameter CLK_PERIOD = 10ns;
  parameter RESET_TIME = 10*CLK_PERIOD;

  // TRANSACTION FORMAT
  parameter GENERATOR_FL_PACKET_COUNT      = FRAME_PARTS;   // pocet paketov vo frame
  int       GENERATOR_FL_PACKET_SIZE_MAX[] = '{32,1526,32};   // maximalna velkost paketov
  int       GENERATOR_FL_PACKET_SIZE_MIN[] = '{8,64,8};      // minimalna velkost paketov

  // TEST SETTINGS
  parameter TEST_TRANSACTION_COUNT     = 1500;

  // DRIVER0 PARAMETERS
  parameter DRIVER_DATA_WIDTH          = INPUT_WIDTH;      // datova sirka driveru
  parameter DRIVER_DREM_WIDTH          = INPUT_DREM_WIDTH;      // drem sirka driveru
  parameter DRIVER_DELAYEN_WT          = 0;                  // vaha delay enable medzi transakciami
  parameter DRIVER_DELAYDIS_WT         = 3;                  // vaha delay disable medzi transakciami
  parameter DRIVER_DELAYLOW            = 0;                  // spodna hranica delay medzi transakciami
  parameter DRIVER_DELAYHIGH           = 3;                  // horna hranica delay medzi transakciami
  parameter DRIVER_INSIDE_DELAYEN_WT   = 0;                  // vaha delay enable v transakcii
  parameter DRIVER_INSIDE_DELAYDIS_WT  = 3;                  // vaha delay disable v transakcii
  parameter DRIVER_INSIDE_DELAYLOW     = 0;                  // spodna hranica delay v transakcii
  parameter DRIVER_INSIDE_DELAYHIGH    = 3;                  // horna hranica delay v transakcii

  // MONITOR PARAMETERS
  parameter MONITOR_DATA_WIDTH         = OUTPUT_WIDTH;     // datova sirka monitoru
  parameter MONITOR_DREM_WIDTH         = OUTPUT_DREM_WIDTH;     // drem sirka monitoru
  parameter MONITOR_DELAYEN_WT         = 0;                 // vaha delay enable medzi transakciami
  parameter MONITOR_DELAYDIS_WT        = 3;                 // vaha delay disable medzi transakciami
  parameter MONITOR_DELAYLOW           = 0;                 // spodna hranica delay medzi transakciami
  parameter MONITOR_DELAYHIGH          = 3;                 // horna hranica delay medzi transakciami
  parameter MONITOR_INSIDE_DELAYEN_WT  = 0;                 // vaha delay enable v transakcii
  parameter MONITOR_INSIDE_DELAYDIS_WT = 3;                 // vaha delay disable v transakcii
  parameter MONITOR_INSIDE_DELAYLOW    = 0;                 // spodna hranica delay v transakcii
  parameter MONITOR_INSIDE_DELAYHIGH   = 3;                 // horna hranica delay v transakcii

endpackage
