/*
 * test_pkg.sv: Test package
 * Copyright (C) 2014 CESNET
 * Author: Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
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

   import math_pkg::*;       // log2()

   // Include this file if you want to use standard SystemVerilog Scoreboard
   `include "scoreboard.sv"

   parameter DATA_WIDTH    = 512;        // Data width
   parameter SOP_POS_WIDTH = 3;
   parameter EOP_POS_WIDTH = log2(DATA_WIDTH/8);     // Data Reminder width

   // CLOCKS AND RESETS
   parameter APP_CLK_PERIOD = 5ns;
   parameter QDR_CLK_PERIOD = 3ns;
   parameter APP_RST_TIME = 12*APP_CLK_PERIOD;
   parameter QDR_RST_TIME = 20*QDR_CLK_PERIOD;

   // TRANSACTION FORMAT (GENERATOR 0)
   // maximalna velkost paketov
   int       GENERATOR0_FLU_PACKET_SIZE_MAX = 96;
   // minimalna velkost paketov
   int       GENERATOR0_FLU_PACKET_SIZE_MIN = 8;

   // DRIVER0 PARAMETERS
   // datova sirka driveru
   parameter DRIVER0_DATA_WIDTH         = DATA_WIDTH;
   parameter DRIVER0_SOP_WIDTH          = SOP_POS_WIDTH;
   parameter DRIVER0_EOP_WIDTH          = EOP_POS_WIDTH;
   // vaha delay enable medzi transakciami
   parameter DRIVER0_DELAYEN_WT         = 1;
   // vaha delay disable medzi transakciami
   parameter DRIVER0_DELAYDIS_WT        = 50;
   // spodna hranica delay medzi transakciami
   parameter DRIVER0_DELAYLOW           = 0;
   // horna hranica delay medzi transakciami
   parameter DRIVER0_DELAYHIGH          = 10;
   // vaha delay enable v transakcii
   parameter DRIVER0_INSIDE_DELAYEN_WT  = 1;
   // vaha delay disable v transakcii
   parameter DRIVER0_INSIDE_DELAYDIS_WT = 50;
   // spodna hranica delay v transakcii
   parameter DRIVER0_INSIDE_DELAYLOW    = 0;
   // horna hranica delay v transakcii
   parameter DRIVER0_INSIDE_DELAYHIGH   = 10;
   parameter DRIVER0_START_POS_LOW      = 0;
   parameter DRIVER0_START_POS_HIGH     = 2**SOP_POS_WIDTH-1;


   // MONITOR0 PARAMETERS
   // vaha delay enable medzi transakciami
   parameter MONITOR0_DELAYEN_WT         = 1;
   // vaha delay disable medzi transakciami
   parameter MONITOR0_DELAYDIS_WT        = 50;
   // spodna hranica delay medzi transakciami
   parameter MONITOR0_DELAYLOW           = 0;
   // horna hranica delay medzi transakciami
   parameter MONITOR0_DELAYHIGH          = 10;
   // vaha delay enable v transakcii
   parameter MONITOR0_INSIDE_DELAYEN_WT  = 1;
   // vaha delay disable v transakcii
   parameter MONITOR0_INSIDE_DELAYDIS_WT = 50;
   // spodna hranica delay v transakcii
   parameter MONITOR0_INSIDE_DELAYLOW    = 0;
   // horna hranica delay v transakcii
   parameter MONITOR0_INSIDE_DELAYHIGH   = 10;


   // TEST PARAMETERS
   parameter TRANSACTION_COUNT = 1000000; // Count of transactions to generate

endpackage
