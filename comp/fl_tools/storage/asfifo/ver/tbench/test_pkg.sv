/*
 * test_pkg.sv: Test package
 * Copyright (C) 2009 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
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

   // Include this file if you want to use standard SystemVerilog Scoreboard
   `include "scoreboard.sv"


   // DUT GENERICS
   parameter RX_DATA_WIDTH = 128;            // datova sirka RX
   parameter RX_DREM_WIDTH = 4;             // drem  sirka RX
   parameter TX_DATA_WIDTH = 128;            // datova sirka TX
   parameter TX_DREM_WIDTH = 4;             // drem sirka TX


   // CLOCKS AND RESETS
   parameter RX_CLK_PERIOD = 5ns;
   parameter RX_RESET_TIME = 20*RX_CLK_PERIOD;
   parameter TX_CLK_PERIOD = 18ns;
   parameter TX_RESET_TIME = 10*TX_CLK_PERIOD;

   // TRANSACTION FORMAT (GENERATOR 0)
   parameter GENERATOR0_FL_PACKET_COUNT      = 3;                // pocet paketov vo frame
   int       GENERATOR0_FL_PACKET_SIZE_MAX[] = '{16,256,32};      // maximalna velkost paketov
   int       GENERATOR0_FL_PACKET_SIZE_MIN[] = '{1,1,1};         // minimalna velkost paketov

   // DRIVER0 PARAMETERS
   parameter DRIVER0_DATA_WIDTH         = RX_DATA_WIDTH;         // datova sirka driveru
   parameter DRIVER0_DREM_WIDTH         = RX_DREM_WIDTH;         // drem sirka driveru
   parameter DRIVER0_DELAYEN_WT         = 1;                     // vaha delay enable medzi transakciami
   parameter DRIVER0_DELAYDIS_WT        = 50;                     // vaha delay disable medzi transakciami
   parameter DRIVER0_DELAYLOW           = 0;                     // spodna hranica delay medzi transakciami
   parameter DRIVER0_DELAYHIGH          = 10;                     // horna hranica delay medzi transakciami
   parameter DRIVER0_INSIDE_DELAYEN_WT  = 1;                     // vaha delay enable v transakcii
   parameter DRIVER0_INSIDE_DELAYDIS_WT = 50;                     // vaha delay disable v transakcii
   parameter DRIVER0_INSIDE_DELAYLOW    = 0;                     // spodna hranica delay v transakcii
   parameter DRIVER0_INSIDE_DELAYHIGH   = 10;                     // horna hranica delay v transakcii

   // MONITOR0 PARAMETERS
   parameter MONITOR0_DATA_WIDTH         = TX_DATA_WIDTH;         // datova sirka monitoru
   parameter MONITOR0_DREM_WIDTH         = TX_DREM_WIDTH;         // drem sirka monitoru
   parameter MONITOR0_DELAYEN_WT         = 1;                     // vaha delay enable medzi transakciami
   parameter MONITOR0_DELAYDIS_WT        = 5;                     // vaha delay disable medzi transakciami
   parameter MONITOR0_DELAYLOW           = 5;                     // spodna hranica delay medzi transakciami
   parameter MONITOR0_DELAYHIGH          = 10;                     // horna hranica delay medzi transakciami
   parameter MONITOR0_INSIDE_DELAYEN_WT  = 1;                     // vaha delay enable v transakcii
   parameter MONITOR0_INSIDE_DELAYDIS_WT = 50;                     // vaha delay disable v transakcii
   parameter MONITOR0_INSIDE_DELAYLOW    = 1;                     // spodna hranica delay v transakcii
   parameter MONITOR0_INSIDE_DELAYHIGH   = 10;                     // horna hranica delay v transakcii


   // TEST PARAMETERS
   parameter TRANSACTION_COUNT = 2000; // Count of transactions to generate

endpackage
