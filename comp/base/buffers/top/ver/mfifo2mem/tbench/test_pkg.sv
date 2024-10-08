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

   // Include scoreboard and coverage
   `include "scoreboard.sv"
   `include "command_coverage.sv"


   // -- MFIFO2MEM PARAMETERS -----------------------------
    // Data width
   parameter DATA_WIDTH      = 64;
    // Number of flows
   parameter FLOWS           = 4;
    // Max count of items stored for one block
   parameter BLOCK_SIZE      = 512;
    // Type of data memory (0 = BRAM, 1 = LUT)
   parameter LUT_MEMORY      = 0;
    // Use output register (1 = true)
   parameter OUTPUT_REG      = 0;

   // -- TESTBENT PARAMETERS ------------------------------
    // CLOCKS AND RESETS
   parameter CLK_PERIOD = 10ns;
   parameter RESET_TIME = 10*CLK_PERIOD;

   // -- TRANSACTION PARAMETERS ---------------------------
   parameter GENERATOR0_DATA_SIZE      = DATA_WIDTH;
   parameter GENERATOR0_FLOW_COUNT     = FLOWS;

   // -- MFIFO DRIVER PARAMETERS --------------------------
   parameter DRIVER0_DATA_WIDTH         = DATA_WIDTH;
   parameter DRIVER0_FLOWS              = FLOWS;
   parameter DRIVER0_BLOCK_SIZE         = BLOCK_SIZE;
   parameter DRIVER0_LUT_MEMORY         = LUT_MEMORY;
    // Delay enable weight
   parameter DRIVER0_DELAYEN_WT         = 1;
    // Delay disable weight
   parameter DRIVER0_DELAYDIS_WT        = 10;
    // Lower limit of delay time
   parameter DRIVER0_DELAYLOW           = 0;
    // Upper limit of delay time
   parameter DRIVER0_DELAYHIGH          = 10;

   // -- MEMORY MONITOR PARAMETERS -----------------------
   parameter MONITOR0_DATA_WIDTH        = DATA_WIDTH;
   parameter MONITOR0_FLOWS             = FLOWS;
   parameter MONITOR0_BLOCK_SIZE        = BLOCK_SIZE;
   parameter MONITOR0_LUT_MEMORY        = LUT_MEMORY;
   parameter MONITOR0_OUTPUT_REG        = OUTPUT_REG;
    // READ delay enable weight
   parameter MONITOR0_DELAYEN_WT        = 1;
    // READ delay disable weight
   parameter MONITOR0_DELAYDIS_WT       = 3;
    // PIPE_EN delay enable weight
   parameter MONITOR0_PIPEEN_WT         = 1;
    // PIPE_EN delay disable weight
   parameter MONITOR0_PIPEDIS_WT        = 3;


   // -- TEST PARAMETERS ---------------------------------
    // Count of transactions to generate
   parameter TRANSACTION_COUNT = 5000;

endpackage
