/*
 * test_pkg.sv: Test package
 * Copyright (C) 2012 CESNET
 * Author(s): Pavel Benacek <benacek@cesnet.cz>
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

    import sv_common_pkg::TRUE, sv_common_pkg::FALSE;
    import math_pkg::*;       // log2()

   // Include this file if you want to use C plus plus Scoreboard
   // `include "dpi/dpi_scoreboard.sv"

   // DUT GENERICS
   parameter DATA_WIDTH    = 512;
   parameter SOP_POS_WIDTH = 3;
   parameter PORTS         = 8;

   parameter DIVISION_RATIO   = 2;
   parameter PIPELINE_MAP     = 42;
   parameter DSP_MAP          = 21;
   parameter ALIGN_MAP        = 255;
   parameter HDR_ENABLE       = TRUE;
   parameter ENABLE_DEBUG     = TRUE;
   parameter HDR_WIDTH        = 128;
   parameter HDR_FIFO_ITEMS   = 16;
   parameter RESERVE_GAP_EN   = TRUE;

   parameter GAP_SIZE_MIN     = 16; // in bytes
   parameter GAP_SIZE_MAX     = -1; // infinity :)

   // OTHER PARAMETERS (computed from generics)
   parameter EOP_POS_WIDTH=log2(DATA_WIDTH/8);
   parameter HDR_EOP_POS_WIDTH=log2(HDR_WIDTH/8);
   parameter HDR_SOP_POS_WIDTH=1;

   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // TRANSACTION FORMAT (GENERATOR 0)
   parameter GENERATOR0_FLU_PACKET_COUNT    = 1;                  // pocet paketov vo frame
   int       GENERATOR0_FLU_PACKET_SIZE_MAX = 256;                // maximalna velkost paketov
   int       GENERATOR0_FLU_PACKET_SIZE_MIN = 60;                 // minimalna velkost paketov

   // TRANSACTION FORMAT (HEADER GENERATOR)
   int GENERATOR_FL_PACKET_SIZE_MIN = HDR_WIDTH/8;
   int GENERATOR_FL_PAKCET_SIZE_MAX = HDR_WIDTH/8;

   // TEST PARAMETERS
   parameter TRANSACTION_COUNT = 1000; // Count of transactions to generate

   // Data ------------------------------------------------------------------------------
   // DRIVER0 PARAMETERS
   parameter DRIVER0_DATA_WIDTH         = DATA_WIDTH;         // datova sirka driveru
   parameter DRIVER0_EOP_WIDTH          = EOP_POS_WIDTH;
   parameter DRIVER0_SOP_WIDTH          = SOP_POS_WIDTH;
   parameter DRIVER0_INSIDE_DELAYEN_WT  = 1;                     // vaha delay enable v transakcii
   parameter DRIVER0_INSIDE_DELAYDIS_WT = 1;                     // vaha delay disable v transakcii
   parameter DRIVER0_INSIDE_DELAYLOW    = 0;                     // spodna hranica delay v transakcii
   parameter DRIVER0_INSIDE_DELAYHIGH   = 3;                     // horna hranica delay v transakcii
   parameter DRIVER0_START_POS_LOW      = 0;
   parameter DRIVER0_START_POS_HIGH     = 2**SOP_POS_WIDTH-1;

   // MONITOR0 PARAMETERS
   parameter MONITOR0_DELAYEN_WT         = 1;                     // vaha delay enable medzi transakciami
   parameter MONITOR0_DELAYDIS_WT        = 1;                     // vaha delay disable medzi transakciami
   parameter MONITOR0_DELAYLOW           = 0;                     // spodna hranica delay medzi transakciami
   parameter MONITOR0_DELAYHIGH          = 3;                     // horna hranica delay medzi transakciami
   parameter MONITOR0_INSIDE_DELAYEN_WT  = 0;                     // vaha delay enable v transakcii
   parameter MONITOR0_INSIDE_DELAYDIS_WT = 3;                     // vaha delay disable v transakcii
   parameter MONITOR0_INSIDE_DELAYLOW    = 0;                     // spodna hranica delay v transakcii
   parameter MONITOR0_INSIDE_DELAYHIGH   = 3;                     // horna hranica delay v transakcii

   // Header ----------------------------------------------------------------------------
  // DRIVER0 PARAMETERS
  parameter DRIVER_HDR_DATA_WIDTH               = HDR_WIDTH;           // datova sirka driveru
  parameter DRIVER_HDR_EOP_WIDTH                = HDR_EOP_POS_WIDTH;
  parameter DRIVER_HDR_SOP_WIDTH                = HDR_SOP_POS_WIDTH;
  parameter DRIVER_HDR_INSIDE_DELAYEN_WT        = 0;                     // vaha delay enable v transakcii
  parameter DRIVER_HDR_INSIDE_DELAYDIS_WT       = 1;                     // vaha delay disable v transakcii
  parameter DRIVER_HDR_INSIDE_DELAYLOW          = 0;                     // spodna hranica delay v transakcii
  parameter DRIVER_HDR_INSIDE_DELAYHIGH         = 3;                     // horna hranica delay v transakcii
  // Dont' change this parameter!
  parameter DRIVER_HDR_START_POS_LOW            = 0;
  parameter DRIVER_HDR_START_POS_HIGH           = 0;

  // MONITOR PARAMETERS
  parameter MONITOR_HDR_DELAYEN_WT         = 1;                     // vaha delay enable medzi transakciami
  parameter MONITOR_HDR_DELAYDIS_WT        = 1;                     // vaha delay disable medzi transakciami
  parameter MONITOR_HDR_DELAYLOW           = 0;                     // spodna hranica delay medzi transakciami
  parameter MONITOR_HDR_DELAYHIGH          = 3;                     // horna hranica delay medzi transakciami
  parameter MONITOR_HDR_INSIDE_DELAYEN_WT  = 0;                     // vaha delay enable v transakcii
  parameter MONITOR_HDR_INSIDE_DELAYDIS_WT = 3;                     // vaha delay disable v transakcii
  parameter MONITOR_HDR_INSIDE_DELAYLOW    = 0;                     // spodna hranica delay v transakcii
  parameter MONITOR_HDR_INSIDE_DELAYHIGH   = 3;                     // horna hranica delay v transakcii

   // Include this file if you want to use standard SystemVerilog Scoreboard
   `include "scoreboard.sv"

endpackage
