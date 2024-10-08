/*
 * testbench.sv: Top Entity for IB_SWITCH automatic test
 * Copyright (C) 2007 CESNET
 * Author(s): Petr Kobiersky <kobiersky@liberouter.org>
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
  // V PRIPADE VIACERYCH POUZITYCH INTERFACOV JE NUTNE DOPLNENIE ICH DEKLARACIE
  // A TIEZ DO DESIGN UNDER TEST A TEST
  logic            CLK   = 0;
  logic            RESET;
  iFrameLinkRx #(RX_DATA_WIDTH, RX_DREM_WIDTH) RX  (CLK, RESET);
  iFrameLinkTx #(TX_DATA_WIDTH, TX_DREM_WIDTH) TX  (CLK, RESET);
  iFrameLinkTx #(TX_DATA_WIDTH, TX_DREM_WIDTH) MONITOR  (CLK, RESET);


  //-- Clock generation -------------------------------------------------------
  always #(CLK_PERIOD/2) CLK = ~CLK;


  //-- Design Under Test ------------------------------------------------------
  DUT DUT_U   (.CLK     (CLK),
               .RESET   (RESET),
               .RX      (RX),
               .TX      (TX),
               .MONITOR (TX)
              );


  //-- Test -------------------------------------------------------------------
  TEST TEST_U (.CLK          (CLK),
               .RESET        (RESET),
               .RX           (RX),
               .TX           (TX),
               .MONITOR      (TX)
              );

endmodule : testbench
