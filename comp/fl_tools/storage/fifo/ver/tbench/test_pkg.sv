/*
 * test_pkg.sv: Test package
 * Copyright (C) 2007 CESNET
 * Author(s): Petr Kobiersky <kobiersky@liberouter.org>
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

   // DUT GENERICS
   parameter DATA_WIDTH   = 64;        // Data width
   parameter USE_BRAMS    = 1;         // Use BlockBAMs/SelectRAMs
   parameter ITEMS        = 1024;       // Number of items in the FIFO
   parameter BLOCK_SIZE   = 16;       // Size of block (for LSTBLK signal)
   parameter STATUS_WIDTH = 7;         // Width of STATUS signal available
   parameter PARTS        = 3;         // Number of parts in each frame

   parameter DREM_WIDTH   = log2(DATA_WIDTH/8);     // Data Reminder width

   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // TRANSACTION FORMAT (GENERATOR 0)
   // pocet paketov vo frame
   parameter GENERATOR0_FL_PACKET_COUNT      = PARTS;
   // maximalna velkost paketov
   int       GENERATOR0_FL_PACKET_SIZE_MAX[] = '{32, 1536, 32};
   // minimalna velkost paketov
   int       GENERATOR0_FL_PACKET_SIZE_MIN[] = '{1, 64, 1};

   // DRIVER0 PARAMETERS
   // datova sirka driveru
   parameter DRIVER0_DATA_WIDTH         = DATA_WIDTH;
   // drem sirka driveru
   parameter DRIVER0_DREM_WIDTH         = DREM_WIDTH;
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

   // MONITOR0 PARAMETERS
   // datova sirka monitoru
   parameter MONITOR0_DATA_WIDTH         = DATA_WIDTH;
   // drem sirka monitoru
   parameter MONITOR0_DREM_WIDTH         = DREM_WIDTH;
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
   parameter TRANSACTION_COUT = 2000; // Count of transactions to generate

endpackage
