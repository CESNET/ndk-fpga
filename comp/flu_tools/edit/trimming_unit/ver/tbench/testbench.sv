/*
 * testbench.sv: Top Entity for automatic test
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
//                                 TESTBENCH
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

module testbench;
   logic CLK = 0;
   logic RESET;
   lengthInterface #(LENGTH_WIDTH) LENGTH (CLK, RESET);
   iFrameLinkURx #(DATA_WIDTH, EOP_POS_WIDTH, SOP_POS_WIDTH) RX (CLK, RESET);
   iFrameLinkUTx #(DATA_WIDTH, EOP_POS_WIDTH, SOP_POS_WIDTH) TX (CLK, RESET);
   iFrameLinkUTx #(DATA_WIDTH, EOP_POS_WIDTH, SOP_POS_WIDTH) MONITOR (CLK, RESET);

  //-- Clock generation -------------------------------------------------------
  always #(CLK_PERIOD/2) CLK = ~CLK;


  //-- Design Under Test ------------------------------------------------------
  DUT DUT_U   (.CLK     (CLK),
               .RESET   (RESET),
               .LENGTH  (LENGTH),
               .RX      (RX),
               .TX      (TX)
              );


  //-- Test -------------------------------------------------------------------
  TEST TEST_U (.CLK          (CLK),
               .RESET        (RESET),
               .LENGTH       (LENGTH),
               .RX           (RX),
               .TX           (TX),
               .MONITOR      (TX)
              );

endmodule : testbench
