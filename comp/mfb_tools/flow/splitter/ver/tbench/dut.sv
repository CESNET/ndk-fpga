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
   iMfbRx.dut RX_MFB,
   iMvbTx.dut TX_MVB[SPLITTER_OUTPUTS-1:0],
   iMfbTx.dut TX_MFB[SPLITTER_OUTPUTS-1:0]
);

localparam SOF_WIDTH = math_pkg::max(1,$clog2(MFB_REGION_SIZE));
localparam EOF_WIDTH = math_pkg::max(1,$clog2(MFB_REGION_SIZE*MFB_BLOCK_SIZE));

logic [SPLITTER_OUTPUTS-1:0] [MVB_ITEMS*HDR_WIDTH-1:0] tx_mvb_data   ;
logic [SPLITTER_OUTPUTS-1:0] [MVB_ITEMS          -1:0] tx_mvb_vld    ;
logic [SPLITTER_OUTPUTS-1:0]                           tx_mvb_src_rdy;
logic [SPLITTER_OUTPUTS-1:0]                           tx_mvb_dst_rdy;

logic [SPLITTER_OUTPUTS-1:0] [MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1:0] tx_mfb_data   ;
logic [SPLITTER_OUTPUTS-1:0] [MFB_REGIONS                                              -1:0] tx_mfb_sof    ;
logic [SPLITTER_OUTPUTS-1:0] [MFB_REGIONS                                              -1:0] tx_mfb_eof    ;
logic [SPLITTER_OUTPUTS-1:0] [MFB_REGIONS*SOF_WIDTH                                    -1:0] tx_mfb_sof_pos;
logic [SPLITTER_OUTPUTS-1:0] [MFB_REGIONS*EOF_WIDTH                                    -1:0] tx_mfb_eof_pos;
logic [SPLITTER_OUTPUTS-1:0]                                                                 tx_mfb_src_rdy;
logic [SPLITTER_OUTPUTS-1:0]                                                                 tx_mfb_dst_rdy;

   generate
      for (genvar i = 0; i < SPLITTER_OUTPUTS; i++) begin
         assign TX_MVB[i].DATA    = tx_mvb_data   [i];
         assign TX_MVB[i].VLD     = tx_mvb_vld    [i];
         assign TX_MVB[i].SRC_RDY = tx_mvb_src_rdy[i];
         assign tx_mvb_dst_rdy[i] = TX_MVB[i].DST_RDY;
         assign TX_MFB[i].DATA    = tx_mfb_data   [i];
         assign TX_MFB[i].SOF     = tx_mfb_sof    [i];
         assign TX_MFB[i].EOF     = tx_mfb_eof    [i];
         assign TX_MFB[i].SOF_POS = tx_mfb_sof_pos[i];
         assign TX_MFB[i].EOF_POS = tx_mfb_eof_pos[i];
         assign TX_MFB[i].SRC_RDY = tx_mfb_src_rdy[i];
         assign tx_mfb_dst_rdy[i] = TX_MFB[i].DST_RDY;
      end
   endgenerate

   DUT_WRAPPER #(
      .SPLITTER_OUTPUTS (SPLITTER_OUTPUTS),
      .HDR_WIDTH        (HDR_WIDTH),
      .MFB_REGIONS      (MFB_REGIONS),
      .MFB_REGION_SIZE  (MFB_REGION_SIZE),
      .MFB_BLOCK_SIZE   (MFB_BLOCK_SIZE),
      .MFB_ITEM_WIDTH   (MFB_ITEM_WIDTH),
      .MVB_ITEMS        (MVB_ITEMS),
      .MVB_ITEM_WIDTH   (MVB_ITEM_WIDTH)
   ) VHDL_DUT_U (
      .CLK            (CLK),
      .RESET          (RESET),

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

      .TX_MVB_DATA    (tx_mvb_data),
      .TX_MVB_VLD     (tx_mvb_vld),
      .TX_MVB_SRC_RDY (tx_mvb_src_rdy),
      .TX_MVB_DST_RDY (tx_mvb_dst_rdy),

      .TX_MFB_DATA    (tx_mfb_data),
      .TX_MFB_SOF_POS (tx_mfb_sof_pos),
      .TX_MFB_EOF_POS (tx_mfb_eof_pos),
      .TX_MFB_SOF     (tx_mfb_sof),
      .TX_MFB_EOF     (tx_mfb_eof),
      .TX_MFB_SRC_RDY (tx_mfb_src_rdy),
      .TX_MFB_DST_RDY (tx_mfb_dst_rdy)
    );

endmodule
