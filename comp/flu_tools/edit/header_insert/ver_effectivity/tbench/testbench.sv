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
  iFrameLinkURx #(DATA_WIDTH, EOP_POS_WIDTH, SOP_POS_WIDTH) RX       (CLK, RESET);
  iFrameLinkURx #(HDR_WIDTH,  HDR_POS_WIDTH, 1)             HDR      (CLK, RESET);
  iFrameLinkUTx #(DATA_WIDTH, EOP_POS_WIDTH, SOP_POS_WIDTH) TX       (CLK, RESET);


  //-- Clock generation -------------------------------------------------------
  always #(CLK_PERIOD/2) CLK = ~CLK;


  //-- Design Under Test ------------------------------------------------------
  DUT DUT_U   (.CLK     (CLK),
               .RESET   (RESET),
               .RX      (RX),
               .TX      (TX),
               .HDR     (HDR)
              );


  //-- Test -------------------------------------------------------------------
  TEST TEST_U (.CLK     (CLK),
               .RESET   (RESET),
               .RX      (RX),
               .HDR     (HDR),
               .TX      (TX),
               .MONITOR (TX)
              );

endmodule : testbench
