/*
 * test_pkg.sv: Test package
 * Copyright (C) 2012 CESNET
 * Author(s): Lukas Kekely <kekely@cesnet.cz>
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

   // Include this file if you want to use C plus plus Scoreboard
   // `include "dpi/dpi_scoreboard.sv"

   // DUT GENERICS
   parameter RX_DWIDTH = 256;            // datova sirka RX
   parameter RX_EOPWIDTH=5;
   parameter RX_SOPWIDTH=2;
   parameter MAX_RATE=16;
   parameter MAX_RATE_L=4;
   parameter DUT_RATE=3;

   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // TRANSACTION FORMAT (GENERATOR 0)
   parameter GENERATOR0_FLU_PACKET_COUNT      = 1;                // pocet paketov vo frame
   int       GENERATOR0_FLU_PACKET_SIZE_MAX = 96;      // maximalna velkost paketov
   int       GENERATOR0_FLU_PACKET_SIZE_MIN = 8;         // minimalna velkost paketov

   // DRIVER0 PARAMETERS
   parameter DRIVER0_DATA_WIDTH         = RX_DWIDTH;         // datova sirka driveru
   parameter DRIVER0_EOP_WIDTH          = RX_EOPWIDTH;
   parameter DRIVER0_SOP_WIDTH          = RX_SOPWIDTH;
   parameter DRIVER0_INSIDE_DELAYEN_WT  = 1;                     // vaha delay enable v transakcii
   parameter DRIVER0_INSIDE_DELAYDIS_WT = 3;                     // vaha delay disable v transakcii
   parameter DRIVER0_INSIDE_DELAYLOW    = 0;                     // spodna hranica delay v transakcii
   parameter DRIVER0_INSIDE_DELAYHIGH   = 3;                     // horna hranica delay v transakcii
   parameter DRIVER0_START_POS_LOW      = 0;
   parameter DRIVER0_START_POS_HIGH     = 3;                     // 2**SOP_WIDTH-1

   // MONITOR0 PARAMETERS
   parameter MONITOR0_DELAYEN_WT         = 1;                     // vaha delay enable medzi transakciami
   parameter MONITOR0_DELAYDIS_WT        = 3;                     // vaha delay disable medzi transakciami
   parameter MONITOR0_DELAYLOW           = 0;                     // spodna hranica delay medzi transakciami
   parameter MONITOR0_DELAYHIGH          = 3;                     // horna hranica delay medzi transakciami
   parameter MONITOR0_INSIDE_DELAYEN_WT  = 1;                     // vaha delay enable v transakcii
   parameter MONITOR0_INSIDE_DELAYDIS_WT = 3;                     // vaha delay disable v transakcii
   parameter MONITOR0_INSIDE_DELAYLOW    = 0;                     // spodna hranica delay v transakcii
   parameter MONITOR0_INSIDE_DELAYHIGH   = 3;                     // horna hranica delay v transakcii


   // TEST PARAMETERS
   parameter TRANSACTION_COUNT = 10000; // Count of transactions to generate

endpackage
