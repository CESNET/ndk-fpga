/*
 * testbench.sv: Top Entity for AS_FIFO automatic test
 * Copyright (C) 2009 CESNET
 * Author(s): Marek Santa <xsanta06@stud.fit.vutbr.cz>
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
  logic            RX_CLK   = 0;
  logic            RX_RESET;
  logic            TX_CLK   = 0;
  logic            TX_RESET;
  iFrameLinkRx #(RX_DATA_WIDTH, RX_DREM_WIDTH) RX  (RX_CLK, RX_RESET);
  iFrameLinkTx #(TX_DATA_WIDTH, TX_DREM_WIDTH) TX  (TX_CLK, TX_RESET);


  //-- Clock generation -------------------------------------------------------
  always #(RX_CLK_PERIOD/2) RX_CLK = ~RX_CLK;
  always #(TX_CLK_PERIOD/2) TX_CLK = ~TX_CLK;


  //-- Design Under Test ------------------------------------------------------
  DUT DUT_U   (.RX_CLK     (RX_CLK),
               .RX_RESET   (RX_RESET),
               .TX_CLK     (TX_CLK),
               .TX_RESET   (TX_RESET),
               .RX         (RX),
               .TX         (TX)
              );


  //-- Test -------------------------------------------------------------------
  TEST TEST_U (.RX_CLK     (RX_CLK),
               .RX_RESET   (RX_RESET),
               .TX_CLK     (TX_CLK),
               .TX_RESET   (TX_RESET),
               .RX         (RX),
               .TX         (TX),
               .MONITOR    (TX)
              );

endmodule : testbench
