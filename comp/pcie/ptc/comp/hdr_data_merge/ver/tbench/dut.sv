/*!
 * \file dut.sv
 * \brief Design Under Test
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

module DUT (
   input logic DMA_CLK,
   input logic DMA_RESET,
   input logic PCIE_CLK,
   input logic PCIE_RESET,
   iMvbRx.dut RX_MVB,
   iMfbRx.dut RX_MFB,
   iMfbTx.dut TX_MFB
);

   DUT_WRAPPER #(
      .MFB_REGIONS         (MFB_REGIONS),
      .MFB_REGION_SIZE     (MFB_REGION_SIZE),
      .MFB_BLOCK_SIZE      (MFB_BLOCK_SIZE),
      .MFB_ITEM_WIDTH      (MFB_ITEM_WIDTH),
      .MVB_ITEMS           (MVB_ITEMS),
      .MVB_ITEM_WIDTH      (MVB_ITEM_WIDTH),
      .MAX_PCIE_TRANS_SIZE (PAYLOAD_SIZE_MAX+4)
   ) VHDL_DUT_U (
      .DMA_CLK        (DMA_CLK),
      .DMA_RESET      (DMA_RESET),

      .PCIE_CLK       (PCIE_CLK),
      .PCIE_RESET     (PCIE_RESET),

      .RX_MVB_DATA    (RX_MVB.DATA),
      .RX_MVB_VLD     (RX_MVB.VLD),
      .RX_MVB_SRC_RDY (RX_MVB.SRC_RDY),
      .RX_MVB_DST_RDY (RX_MVB.DST_RDY),

      .RX_MFB_DATA    (RX_MFB.DATA),
      .RX_MFB_SOF_POS (RX_MFB.SOF_POS),
      .RX_MFB_EOF_POS (RX_MFB.EOF_POS),
      .RX_MFB_SOF     (RX_MFB.SOF),
      .RX_MFB_EOF     (RX_MFB.EOF),
      .RX_MFB_SRC_RDY (RX_MFB.SRC_RDY),
      .RX_MFB_DST_RDY (RX_MFB.DST_RDY),

      .TX_MFB_DATA    (TX_MFB.DATA),
      .TX_MFB_SOF_POS (TX_MFB.SOF_POS),
      .TX_MFB_EOF_POS (TX_MFB.EOF_POS),
      .TX_MFB_SOF     (TX_MFB.SOF),
      .TX_MFB_EOF     (TX_MFB.EOF),
      .TX_MFB_SRC_RDY (TX_MFB.SRC_RDY),
      .TX_MFB_DST_RDY (TX_MFB.DST_RDY),
      .TX_MFB_BE      ()
    );

endmodule
