/*
 * testbench.sv: Top Entity for IB_SWITCH automatic test
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

  logic            CLK   = 0;
  logic            RESET;
  logic[MAX_RATE_L-1:0] RATE;
  logic            PCKT_DISCARD;
  iFrameLinkURx #(RX_DWIDTH, RX_EOPWIDTH, RX_SOPWIDTH) RX  (CLK, RESET);
  iFrameLinkUTx #(RX_DWIDTH, RX_EOPWIDTH, RX_SOPWIDTH) TX  (CLK, RESET);
  iFrameLinkUTx #(RX_DWIDTH, RX_EOPWIDTH, RX_SOPWIDTH) MONITOR  (CLK, RESET);


  //-- Clock generation -------------------------------------------------------
  always #(CLK_PERIOD/2) CLK = ~CLK;


  //-- Design Under Test ------------------------------------------------------
  DUT DUT_U   (.CLK     (CLK),
               .RESET   (RESET),
               .RATE    (RATE),
               .PCKT_DISCARD (PCKT_DISCARD),
               .RX      (RX),
               .TX      (TX),
               .MONITOR (TX)
              );


  //-- Test -------------------------------------------------------------------
  TEST TEST_U (.CLK          (CLK),
               .RESET        (RESET),
               .RATE    (RATE),
               .PCKT_DISCARD (PCKT_DISCARD),
               .RX           (RX),
               .TX           (TX),
               .MONITOR      (TX)
              );

endmodule : testbench
