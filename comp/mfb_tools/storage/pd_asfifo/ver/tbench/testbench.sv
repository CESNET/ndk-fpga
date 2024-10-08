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

   logic RESET;
   logic RX_CLK = 0;
   logic RX_RESET;
   logic TX_CLK = 0;
   logic TX_RESET;

   iMfbRx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) RX(RX_CLK, RX_RESET);
   iMfbTx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) TX(TX_CLK, TX_RESET);
   iMvbRx #(1,1)       FD_RX(RX_CLK, RX_RESET);
   iMvbTx #(REGIONS,1) FD_TX(RX_CLK, RX_RESET);

   always #(RX_CLK_PERIOD/2) RX_CLK = ~RX_CLK;
   always #(TX_CLK_PERIOD/2) TX_CLK = ~TX_CLK;

   always @(posedge RX_CLK) RX_RESET = RESET;
   always @(posedge TX_CLK) TX_RESET = RESET;

   DUT DUT_U (
      .RX_CLK   (RX_CLK),
      .TX_CLK   (TX_CLK),
      .RX_RESET (RX_RESET),
      .TX_RESET (TX_RESET),
      .RX       (RX),
      .TX       (TX),
      .FD_RX    (FD_RX),
      .FD_TX    (FD_TX)
   );

   TEST TEST_U (
      .RX_CLK        (RX_CLK),
      .TX_CLK        (TX_CLK),
      .RESET         (RESET),
      .FD_RX         (FD_RX),
      .FD_TX         (FD_TX),
      .FD_TX_MONITOR (FD_TX),
      .RX            (RX),
      .TX            (TX),
      .TX_MONITOR    (TX)
   );

endmodule
