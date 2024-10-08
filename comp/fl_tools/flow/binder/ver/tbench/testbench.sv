/*
 * testbench.sv: Top Entity for FL_BINDER automatic test
 * Copyright (C) 2008 CESNET
 * Author(s): Martin Kosek <kosek@liberouter.org>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 */


// ----------------------------------------------------------------------------
//                                 TESTBENCH
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

module testbench;

  // -- Testbench wires and interfaces ----------------------------------------
  logic            CLK   = 0;
  logic            RESET;
  iFrameLinkRx #(INPUT_WIDTH, INPUT_DREM_WIDTH) RX[INPUT_COUNT] (CLK, RESET);
  iFrameLinkTx #(OUTPUT_WIDTH, OUTPUT_DREM_WIDTH) TX            (CLK, RESET);

  //-- Clock generation -------------------------------------------------------
  always #(CLK_PERIOD/2) CLK = ~CLK;

  //-- Design Under Test ------------------------------------------------------
  DUT DUT_U   (.CLK     (CLK),
               .RESET   (RESET),
               .RX      (RX),
               .TX      (TX)
              );


  //-- Test -------------------------------------------------------------------
  TEST TEST_U (.CLK          (CLK),
               .RESET        (RESET),
               .RX           (RX),
               .TX           (TX),
               .MONITOR      (TX)
              );

endmodule : testbench
