/*!
 * \file testbench.sv
 * \brief Testbench
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2018
 */
 /*
 * Copyright (C) 2018 CESNET
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

   iMvbRx #(MVB_ITEMS,DMA_DOWNHDR_WIDTH) RX_MVB(CLK, RESET);
   iMfbRx #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH) RX_MFB(CLK, RESET);
   iDMABusTx #(MFB_REGIONS*MFB_REG_WIDTH, DMA_DOWNHDR_WIDTH) TX_DMA(CLK, RESET);

   always #(CLK_PERIOD/2) CLK = ~CLK;

   DUT DUT_U (
      .CLK     (CLK),
      .RESET   (RESET),
      .RX_MVB  (RX_MVB),
      .RX_MFB  (RX_MFB),
      .TX_DMA  (TX_DMA)
   );

   TEST TEST_U (
      .CLK     (CLK),
      .RESET   (RESET),
      .RX_MVB  (RX_MVB),
      .RX_MFB  (RX_MFB),
      .TX_DMA  (TX_DMA),
      .MO_DMA  (TX_DMA)
   );

endmodule
