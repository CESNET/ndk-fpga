/*
 * testbench.sv: Top Entity for automatic test
 * Copyright (C) 2013 CESNET
 * Author: Lukas Kekely <kekely@cesnet.cz>
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

  // -- Testbench wires and interfaces ----------------------------------------
  logic            CLK   = 0;
  logic            RESET;
  iFrameLinkUPRx #(RX_DATA_WIDTH, RX_EOP_POS_WIDTH, RX_SOP_POS_WIDTH_FIX, HEADER_WIDTH, CHANNEL_WIDTH) RX       (CLK, RESET);
  iFrameLinkUPTx #(TX_DATA_WIDTH, TX_EOP_POS_WIDTH, TX_SOP_POS_WIDTH_FIX, HEADER_WIDTH, CHANNEL_WIDTH) TX       (CLK, RESET);


  //-- Clock generation -------------------------------------------------------
  always #(CLK_PERIOD/2) CLK = ~CLK;


  //-- Design Under Test ------------------------------------------------------
  DUT DUT_U   (.CLK     (CLK),
               .RESET   (RESET),
               .RX      (RX),
               .TX      (TX)
              );


  //-- Test -------------------------------------------------------------------
  TEST TEST_U (.CLK     (CLK),
               .RESET   (RESET),
               .RX      (RX),
               .TX      (TX),
               .MONITOR (TX)
              );

endmodule : testbench
