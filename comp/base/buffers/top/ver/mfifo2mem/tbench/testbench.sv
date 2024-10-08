/*
 * testbench.sv: Top Entity for automatic test
 * Copyright (C) 2010 CESNET
 * Author(s): Marek Santa <santa@liberouter.org>
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
  iNFifoTx #(DATA_WIDTH, FLOWS, BLOCK_SIZE, LUT_MEMORY, 0) FW (CLK, RESET);
  // Output interface
  iMemRead #(DATA_WIDTH, FLOWS, BLOCK_SIZE)                MR (CLK, RESET);

  //-- Clock generation -------------------------------------------------------
  // Clock constant in test_pkg
  always #(CLK_PERIOD/2) CLK = ~CLK;

  //-- Unit Under Test --------------------------------------------------------
  DUT DUT_U            (.CLK          (CLK),
                        .RESET        (RESET),
                        .FW           (FW),
                        .MR           (MR)
                       );

  //-- Test -------------------------------------------------------------------
  TEST TEST_U          (.CLK          (CLK),
                        .RESET        (RESET),
                        .FW           (FW),
                        .MR           (MR)
                        );
endmodule : testbench
