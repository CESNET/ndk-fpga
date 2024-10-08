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
  logic        MASTER_CLK   = 0;
  logic        SLAVE_CLK    = 0;

  logic        MASTER_RESET;
  logic        SLAVE_RESET;

  iMi #(MI_WIDTH, MI_WIDTH, MI_META_WIDTH)  MASTER    (MASTER_CLK, MASTER_RESET);
  iMi #(MI_WIDTH, MI_WIDTH, MI_META_WIDTH)  SLAVE     (SLAVE_CLK, SLAVE_RESET);


  //-- Clock generation -------------------------------------------------------
  always #(MASTER_CLK_PERIOD/2)   MASTER_CLK = ~MASTER_CLK;
  always #(SLAVE_CLK_PERIOD/2)    SLAVE_CLK  = ~SLAVE_CLK;


  //-- Design Under Test ------------------------------------------------------
  DUT DUT_U   (.MASTER_RESET       (MASTER_RESET),
               .SLAVE_RESET        (SLAVE_RESET),
               .MASTER_CLK   (MASTER_CLK),
               .SLAVE_CLK    (SLAVE_CLK),
               .MASTER       (MASTER),
               .SLAVE        (SLAVE)
              );


  //-- Test -------------------------------------------------------------------
  TEST TEST_U (.MASTER_RESET       (MASTER_RESET),
               .SLAVE_RESET        (SLAVE_RESET),
               .MASTER_CLK   (MASTER_CLK),
               .SLAVE_CLK    (SLAVE_CLK),
               .MASTER       (MASTER),
               .SLAVE        (SLAVE)
              );

  asfifo_cov COV();
endmodule : testbench
