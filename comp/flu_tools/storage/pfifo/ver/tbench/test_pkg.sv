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
   parameter DATA_WIDTH = 512;
   parameter SOP_POS_WIDTH=3;
   parameter BLOCK_SIZE=1;
   parameter ITEMS=1024;
   parameter STATUS_WIDTH=1;
   parameter HFIFO_ITEMS=64;
   parameter BRAM_ASFIFO = TRUE;
   parameter BRAM_DEVICE = "7SERIES";
   parameter BRAM_SAFE_RESET = FALSE;
   parameter DISABLE_ASFIFO = FALSE;

   parameter EOP_POS_WIDTH=log2(DATA_WIDTH/8);

   // CLOCKS AND RESETS
   parameter RX_CLK_PERIOD = 5ns;
   parameter RESET_TIME = 10*RX_CLK_PERIOD;
   parameter TX_CLK_PERIOD = 6.4ns;

   // TRANSACTION FORMAT (GENERATOR 0)
   int       GENERATOR0_FLU_PACKET_SIZE_MAX = 1500;      // maximalna velkost paketov
   int       GENERATOR0_FLU_PACKET_SIZE_MIN = 8;         // minimalna velkost paketov

   // DRIVER0 & MONITOR0 PARAMETERS
   parameter DRIVER0_DATA_WIDTH         = DATA_WIDTH;         // datova sirka driveru
   parameter DRIVER0_EOP_WIDTH          = EOP_POS_WIDTH;
   parameter DRIVER0_SOP_WIDTH          = SOP_POS_WIDTH;
   parameter DRIVER0_DELAYEN_WT           = 1;
   parameter DRIVER0_DELAYDIS_WT          = 10;
   parameter DRIVER0_DELAYLOW             = 0;
   parameter DRIVER0_DELAYHIGH            = 5;
   parameter MONITOR0_DELAYEN_WT          = 1;
   parameter MONITOR0_DELAYDIS_WT         = 3;
   parameter MONITOR0_DELAYLOW            = 0;
   parameter MONITOR0_DELAYHIGH           = 5;
   parameter MONITOR0_INSIDE_DELAYEN_WT   = 1;
   parameter MONITOR0_INSIDE_DELAYDIS_WT  = 3;
   parameter MONITOR0_INSIDE_DELAYLOW     = 0;
   parameter MONITOR0_INSIDE_DELAYHIGH    = 5;

   // TEST PARAMETERS
   parameter TRANSACTION_COUNT = 10000; // Count of transactions to generate

endpackage
