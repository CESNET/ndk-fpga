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
   input logic CLK,
   input logic RESET,
   iMvbRx.dut RX_MVB,
   iMfbTx.dut TX_MFB
);

   MFB_USER_PACKET_GEN #(
      .REGIONS     (REGIONS),
      .REGION_SIZE (REGION_SIZE),
      .BLOCK_SIZE  (BLOCK_SIZE),
      .ITEM_WIDTH  (ITEM_WIDTH),
      .LEN_WIDTH   (LEN_WIDTH)
   ) VHDL_DUT_U (
      .CLK         (CLK),
      .RESET       (RESET),

      .GEN_DATA    (RX_MVB.DATA),
      .GEN_VLD     (RX_MVB.VLD),
      .GEN_SRC_RDY (RX_MVB.SRC_RDY),
      .GEN_DST_RDY (RX_MVB.DST_RDY),

      .TX_DATA     (TX_MFB.DATA),
      .TX_SOF_POS  (TX_MFB.SOF_POS),
      .TX_EOF_POS  (TX_MFB.EOF_POS),
      .TX_SOF      (TX_MFB.SOF),
      .TX_EOF      (TX_MFB.EOF),
      .TX_SRC_RDY  (TX_MFB.SRC_RDY),
      .TX_DST_RDY  (TX_MFB.DST_RDY)
    );

endmodule
