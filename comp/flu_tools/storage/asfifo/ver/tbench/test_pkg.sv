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

    import math_pkg::*;       // log2()

   // Include this file if you want to use standard SystemVerilog Scoreboard
   `include "scoreboard.sv"

   // Include this file if you want to use C plus plus Scoreboard
   // `include "dpi/dpi_scoreboard.sv"

   // DUT GENERICS
   parameter DATA_WIDTH = 256;
   parameter SOP_POS_WIDTH=2;
   parameter BLOCK_SIZE=1;
   parameter ITEMS=64;
   parameter STATUS_WIDTH=1;
   parameter AUTO_PIPELINE=0;

   parameter EOP_POS_WIDTH=log2(DATA_WIDTH/8);

   // CLOCKS AND RESETS
   parameter RX_CLK_PERIOD = 5ns;
   parameter RESET_TIME = 10*RX_CLK_PERIOD;
   parameter TX_CLK_PERIOD = 6.4ns;

   // TRANSACTION FORMAT (GENERATOR 0)
   parameter GENERATOR0_FLU_PACKET_COUNT    = 1;         // pocet paketov vo frame
   int       GENERATOR0_FLU_PACKET_SIZE_MAX = 1560;      // maximalna velkost paketov
   int       GENERATOR0_FLU_PACKET_SIZE_MIN = 8;         // minimalna velkost paketov

   // DRIVER0 PARAMETERS
   parameter DRIVER0_DATA_WIDTH         = DATA_WIDTH;         // datova sirka driveru
   parameter DRIVER0_EOP_WIDTH          = EOP_POS_WIDTH;
   parameter DRIVER0_SOP_WIDTH          = SOP_POS_WIDTH;
   parameter DRIVER0_INSIDE_DELAYEN_WT  = 1;                     // vaha delay enable v transakcii
   parameter DRIVER0_INSIDE_DELAYDIS_WT = 3;                     // vaha delay disable v transakcii
   parameter DRIVER0_INSIDE_DELAYLOW    = 0;                     // spodna hranica delay v transakcii
   parameter DRIVER0_INSIDE_DELAYHIGH   = 3;                     // horna hranica delay v transakcii
   parameter DRIVER0_START_POS_LOW      = 0;
   parameter DRIVER0_START_POS_HIGH     = 2**SOP_POS_WIDTH-1;

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
