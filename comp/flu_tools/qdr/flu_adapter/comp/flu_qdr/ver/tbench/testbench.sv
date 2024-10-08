/*
 * testbench.sv: Top Entity for FLU_FIFO automatic test
 * Copyright (C) 2014 CESNET
 * Author: Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
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
  logic            APP_CLK   = 0;
  logic            APP_RST;
  logic            QDR_CLK   = 0;
  logic            QDR_RST;
  iFrameLinkURx #(DATA_WIDTH, EOP_POS_WIDTH, SOP_POS_WIDTH) RX       (APP_CLK, APP_RST);
  iFrameLinkUTx #(DATA_WIDTH, EOP_POS_WIDTH, SOP_POS_WIDTH) TX       (APP_CLK, APP_RST);


  //-- Clock generation -------------------------------------------------------
  always #(APP_CLK_PERIOD/2) APP_CLK = ~APP_CLK;
  always #(QDR_CLK_PERIOD/2) QDR_CLK = ~QDR_CLK;


  //-- Design Under Test ------------------------------------------------------
  DUT DUT_U   (.APP_CLK     (APP_CLK),
               .APP_RST   (APP_RST),
               .QDR_CLK     (QDR_CLK),
               .QDR_RST   (QDR_RST),
               .RX      (RX),
               .TX      (TX)
              );


  //-- Test -------------------------------------------------------------------
  TEST TEST_U (.APP_CLK     (APP_CLK),
               .APP_RST   (APP_RST),
               .QDR_CLK     (QDR_CLK),
               .QDR_RST   (QDR_RST),
               .RX      (RX),
               .TX      (TX),
               .MONITOR (TX)
              );

endmodule : testbench
