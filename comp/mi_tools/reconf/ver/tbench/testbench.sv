/*
 * Copyright (C) 2020 CESNET z. s. p. o.
 * Author(s): Radek Iša <isa@cesnet.cz>
 * SPDX-License-Identifier: BSD-3-Clause
 */

// ----------------------------------------------------------------------------
//                                 TESTBENCH
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

module testbench;

  // -- Testbench wires and interfaces ----------------------------------------
  logic CLK = 0;
  logic RESET;

  iMi #(RX_DATA_WIDTH, ADDR_WIDTH, META_WIDTH)  MASTER(CLK, RESET);
  iMi #(TX_DATA_WIDTH, ADDR_WIDTH, META_WIDTH)  SLAVE (CLK, RESET);


  //-- Clock generation -------------------------------------------------------
  always #(CLK_PERIOD/2) CLK = ~CLK;

  //-- Design Under Test ------------------------------------------------------
  DUT DUT_U   (.CLK          (CLK),
               .RESET        (RESET),
               .RX           (MASTER),
               .TX           (SLAVE)
              );


  //-- Test -------------------------------------------------------------------
  TEST TEST_U (.CLK          (CLK),
               .RESET        (RESET),
               .MASTER       (MASTER),
               .SLAVE        (SLAVE)
              );

// TODO: coverage
//  asfifo_cov COV();
endmodule : testbench
