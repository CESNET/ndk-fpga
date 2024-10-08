/*!
 * \file testbench.sv
 * \brief Testbench
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2014
 */
/*
 * Copyright (C) 2014 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import test_pkg::*; // Test constants

module testbench;
  logic            CLK = 0;
  logic            RESET;
  iFrameLinkURx #(DATA_WIDTH, EOP_POS_WIDTH, SOP_POS_WIDTH) RX (CLK, RESET);
  iFrameLinkUTx #(DATA_WIDTH, EOP_POS_WIDTH, SOP_POS_WIDTH) TX (CLK, RESET);

  //-- Clock generation -------------------------------------------------------
  always #(CLK_PERIOD/2) CLK = ~CLK;

  //-- Design Under Test ------------------------------------------------------
  DUT DUT_U (
    .CLK     (CLK),
    .RESET   (RESET),
    .RX      (RX),
    .TX      (TX)
  );

  //-- Test -------------------------------------------------------------------
  TEST TEST_U (
    .CLK          (CLK),
    .RESET        (RESET),
    .RX           (RX),
    .TX           (TX),
    .MONITOR      (TX)
  );

endmodule : testbench
