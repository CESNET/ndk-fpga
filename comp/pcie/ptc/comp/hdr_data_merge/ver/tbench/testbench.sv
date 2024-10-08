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

   logic DMA_CLK = 0;
   logic DMA_RESET;
   logic PCIE_CLK = 0;
   logic PCIE_RESET;

   iMvbRx #(MVB_ITEMS,MVB_ITEM_WIDTH) RX_MVB(PCIE_CLK, PCIE_RESET);
   iMfbRx #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH) RX_MFB(DMA_CLK, DMA_RESET);
   iMfbTx #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH) TX_MFB(PCIE_CLK, PCIE_RESET);

   always #(DMA_CLK_PERIOD/2) DMA_CLK = ~DMA_CLK;
   always #(PCIE_CLK_PERIOD/2) PCIE_CLK = ~PCIE_CLK;

   DUT DUT_U (
      .DMA_CLK    (DMA_CLK),
      .DMA_RESET  (DMA_RESET),
      .PCIE_CLK   (PCIE_CLK),
      .PCIE_RESET (PCIE_RESET),
      .RX_MVB     (RX_MVB),
      .RX_MFB     (RX_MFB),
      .TX_MFB     (TX_MFB)
   );

   TEST TEST_U (
      .DMA_CLK    (DMA_CLK),
      .DMA_RESET  (DMA_RESET),
      .PCIE_CLK   (PCIE_CLK),
      .PCIE_RESET (PCIE_RESET),
      .RX_MVB     (RX_MVB),
      .RX_MFB     (RX_MFB),
      .TX_MFB     (TX_MFB),
      .MONITOR    (TX_MFB)
   );

endmodule
