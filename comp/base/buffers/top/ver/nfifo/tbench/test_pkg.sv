/*
 * test_pkg.sv: Test package
 * Copyright (C) 2008 CESNET
 * Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
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
   // Include this file if you want to use standard SystemVerilog Coverage
   `include "command_coverage.sv"


   // nastavenie parametrov pre interface, volanie v testbench
   // parametre interface
   parameter DATA_WIDTH      = 16;       // datova sirka
   parameter FLOWS           = 8;        // pocet vystupnych tokov
   parameter BLOCK_SIZE      = 32;       // max pocet poloziek v bloku
   parameter LUT_MEMORY      = 1;        // typ pamati pouzity pre ulozenie dat
   parameter OUTPUT_REG      = 1;        // pridava latenciu 1 takt

   parameter GLOB_STATE      = 0;        // globalny stav

   // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // TRANSACTION FORMAT (GENERATOR 0)
   // sirka dat
   parameter GENERATOR0_DATA_SIZE      = DATA_WIDTH;
   // pocet vystupnych tokov
   parameter GENERATOR0_FLOW_COUNT     = FLOWS;

   // DRIVER0 PARAMETERS
   // datova sirka driveru
   parameter DRIVER0_DATA_WIDTH         = DATA_WIDTH;
   // pocet tokov
   parameter DRIVER0_FLOWS              = FLOWS;
   // sirka bloku
   parameter DRIVER0_BLOCK_SIZE         = BLOCK_SIZE;
   // typ pamate (0 = BRAM, 1 = LUT)
   parameter DRIVER0_LUT_MEMORY         = LUT_MEMORY;
   // globalny stav (0 = )
   parameter DRIVER0_GLOB_STATE         = GLOB_STATE;
   // vaha delay enable medzi transakciami
   parameter DRIVER0_DELAYEN_WT         = 1;
   // vaha delay disable medzi transakciami
   parameter DRIVER0_DELAYDIS_WT        = 3;
   // spodna hranica delay medzi transakciami
   parameter DRIVER0_DELAYLOW           = 0;
   // horna hranica delay medzi transakciami
   parameter DRIVER0_DELAYHIGH          = 3;

   // MONITOR0 PARAMETERS
   // datova sirka monitoru
   parameter MONITOR0_DATA_WIDTH        = DATA_WIDTH;
   // pocet tokov
   parameter MONITOR0_FLOWS             = FLOWS;
   // sirka bloku
   parameter MONITOR0_BLOCK_SIZE        = BLOCK_SIZE;
   // typ pamate (0 = BRAM, 1 = LUT)
   parameter MONITOR0_LUT_MEMORY        = LUT_MEMORY;
   // globalny stav (0 = )
   parameter MONITOR0_GLOB_STATE        = GLOB_STATE;
   // vystupny register
   parameter MONITOR0_OUTPUT_REG        = OUTPUT_REG;
   // vaha delay enable medzi transakciami
   parameter MONITOR0_DELAYEN_WT        = 1;
   parameter MONITOR0_PIPEDELAYEN_WT    = 3;
   // vaha delay disable medzi transakciami
   parameter MONITOR0_DELAYDIS_WT       = 3;
   parameter MONITOR0_PIPEDELAYDIS_WT   = 10;
   // spodna hranica delay medzi transakciami
   parameter MONITOR0_DELAYLOW          = 0;
   parameter MONITOR0_PIPEDELAYLOW      = 2;
   // horna hranica delay medzi transakciami
   parameter MONITOR0_DELAYHIGH         = 3;
   parameter MONITOR0_PIPEDELAYHIGH     = 7;


   // TEST PARAMETERS
   parameter TRANSACTION_COUNT = 100000; // Count of transactions to generate

endpackage
