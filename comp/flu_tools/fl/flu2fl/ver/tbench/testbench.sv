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

  // -- Testbench wires and interfaces ----------------------------------------
  // V PRIPADE VIACERYCH POUZITYCH INTERFACOV JE NUTNE DOPLNENIE ICH DEKLARACIE
  // A TIEZ DO DESIGN UNDER TEST A TEST
  logic            CLK   = 0;
  logic            RESET;
  iFrameLinkURx #(RX_DWIDTH, RX_EOPWIDTH, RX_SOPWIDTH) RX  (CLK, RESET);
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
