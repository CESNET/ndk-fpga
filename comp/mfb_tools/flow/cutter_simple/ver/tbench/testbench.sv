/*!
 * \file testbench.sv
 * \brief Testbench
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2018
 */
 /*
 * Copyright (C) 2018 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import test_pkg::*;

module testbench;

   localparam int CUT_OFFSET_WIDTH = ($clog2(MAX_CUT_OFFSET) > 1) ? $clog2(MAX_CUT_OFFSET) : 1;

   logic CLK = 0;
   logic RESET;
   iMfbRx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH,CUT_OFFSET_WIDTH+1) RX(CLK, RESET);
   iMfbTx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH,CUT_OFFSET_WIDTH+1) TX(CLK, RESET);

   always #(CLK_PERIOD/2) CLK = ~CLK;

   DUT DUT_U (
      .CLK     (CLK),
      .RESET   (RESET),
      .RX      (RX),
      .TX      (TX)
   );

   TEST TEST_U (
      .CLK        (CLK),
      .RESET      (RESET),
      .RX         (RX),
      .TX         (TX),
      .TX_MONITOR (TX)
   );

endmodule
