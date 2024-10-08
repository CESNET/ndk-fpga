/*
 * testbench.sv: Top Entity for automatic test
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
//                                 TESTBENCH
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

module testbench;

  // -- Testbench wires and registers -----------------------------------------
  logic            CLK   = 0;
  logic            RESET;

  // Input interface
  iNFifoRx #(DATA_WIDTH, FLOWS, BLOCK_SIZE, LUT_MEMORY, GLOB_STATE) FW[FLOWS] (CLK, RESET);
  // Output interface
  iNFifoRx #(DATA_WIDTH, FLOWS, BLOCK_SIZE, LUT_MEMORY, GLOB_STATE) FR (CLK, RESET);

  //-- Clock generation -------------------------------------------------------
  // hodiny, konstanta v test_pkg
  always #(CLK_PERIOD/2) CLK = ~CLK;

  //-- Unit Under Test --------------------------------------------------------
  DUT DUT_U                     (.CLK          (CLK),
                                 .RESET        (RESET),
                                 .FW           (FW),
                                 .FR           (FR)
                                );

  //-- Test -------------------------------------------------------------------
  TEST TEST_U          (.CLK          (CLK),
                        .RESET        (RESET),
                        .FW           (FW),
                        .FR           (FR),
                        .MONITOR      (FR)
                        );
endmodule : testbench
