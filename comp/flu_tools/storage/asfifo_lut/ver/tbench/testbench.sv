/*
 * testbench.sv: Top Entity for automatic test
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
//                                 TESTBENCH
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

module testbench;
   logic RX_CLK = 0;
   logic TX_CLK = 0;
   logic RX_RESET;
   logic TX_RESET;
   logic RESET;
   iFrameLinkURx #(DATA_WIDTH, EOP_POS_WIDTH, SOP_POS_WIDTH) RX (RX_CLK, RX_RESET);
   iFrameLinkUTx #(DATA_WIDTH, EOP_POS_WIDTH, SOP_POS_WIDTH) TX (TX_CLK, TX_RESET);

  //-- Clock generation -------------------------------------------------------
  always #(RX_CLK_PERIOD/2) RX_CLK = ~RX_CLK;
  always #(TX_CLK_PERIOD/2) TX_CLK = ~TX_CLK;

  //-- Reset generation -------------------------------------------------------
  always @(posedge RX_CLK) RX_RESET = RESET;
  always @(posedge TX_CLK) TX_RESET = RESET;



  //-- Design Under Test ------------------------------------------------------
  DUT DUT_U   (.RX_CLK      (RX_CLK),
               .RX_RESET    (RX_RESET),
               .TX_CLK      (TX_CLK),
               .TX_RESET    (TX_RESET),
               .RX          (RX),
               .TX          (TX)
              );


  //-- Test -------------------------------------------------------------------
  TEST TEST_U (.RX_CLK      (RX_CLK),
               .TX_CLK      (TX_RESET),
               .RESET       (RESET),
               .RX          (RX),
               .TX          (TX),
               .MONITOR     (TX)
              );

endmodule : testbench
