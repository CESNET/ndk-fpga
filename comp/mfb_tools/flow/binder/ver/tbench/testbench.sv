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

   logic CLK = 0;
   logic RESET;
   iMfbRx #(1,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH)       RX0(CLK, RESET);
   iMfbRx #(1,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH)       RX1(CLK, RESET);
   iMfbRx #(1,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH)       RX2(CLK, RESET);
   iMfbRx #(1,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH)       RX3(CLK, RESET);
   iMfbTx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) TX(CLK, RESET);

   always #(CLK_PERIOD/2) CLK = ~CLK;

   DUT DUT_U (
      .CLK   (CLK),
      .RESET (RESET),
      .RX0   (RX0),
      .RX1   (RX1),
      .RX2   (RX2),
      .RX3   (RX3),
      .TX    (TX)
   );

   TEST TEST_U (
      .CLK     (CLK),
      .RESET   (RESET),
      .RX0     (RX0),
      .RX1     (RX1),
      .RX2     (RX2),
      .RX3     (RX3),
      .TX      (TX),
      .MONITOR (TX)
   );

endmodule
