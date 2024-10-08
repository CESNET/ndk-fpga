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
   iMfbRx.dut RX0,
   iMfbRx.dut RX1,
   iMfbRx.dut RX2,
   iMfbRx.dut RX3,
   iMfbTx.dut TX
);

   localparam DATA_WIDTH = REGIONS * REGION_SIZE * BLOCK_SIZE * ITEM_WIDTH;
   localparam RX_DATA_WIDTH = REGION_SIZE * BLOCK_SIZE * ITEM_WIDTH;
   localparam SOF_POS_WIDTH = REGIONS * $clog2(REGION_SIZE);
   localparam EOF_POS_WIDTH = REGIONS * $clog2(REGION_SIZE * BLOCK_SIZE);

   logic [DATA_WIDTH-1 : 0] rx_data;
   logic [SOF_POS_WIDTH-1 : 0] rx_sof_pos;
   logic [EOF_POS_WIDTH-1 : 0] rx_eof_pos;
   logic [REGIONS-1 : 0] rx_sof;
   logic [REGIONS-1 : 0] rx_eof;
   logic [REGIONS-1 : 0] rx_src_rdy;
   logic [REGIONS-1 : 0] rx_dst_rdy;

   assign rx_data = {RX3.DATA,RX2.DATA,RX1.DATA,RX0.DATA};
   assign rx_sof_pos = {RX3.SOF_POS,RX2.SOF_POS,RX1.SOF_POS,RX0.SOF_POS};
   assign rx_eof_pos = {RX3.EOF_POS,RX2.EOF_POS,RX1.EOF_POS,RX0.EOF_POS};
   assign rx_sof = {RX3.SOF,RX2.SOF,RX1.SOF,RX0.SOF};
   assign rx_eof = {RX3.EOF,RX2.EOF,RX1.EOF,RX0.EOF};
   assign rx_src_rdy = {RX3.SRC_RDY,RX2.SRC_RDY,RX1.SRC_RDY,RX0.SRC_RDY};

   assign RX0.DST_RDY = rx_dst_rdy[0];
   assign RX1.DST_RDY = rx_dst_rdy[1];
   assign RX2.DST_RDY = rx_dst_rdy[2];
   assign RX3.DST_RDY = rx_dst_rdy[3];

   MFB_BINDER #(
      .REGIONS     (REGIONS),
      .REGION_SIZE (REGION_SIZE),
      .BLOCK_SIZE  (BLOCK_SIZE),
      .ITEM_WIDTH  (ITEM_WIDTH)
   ) VHDL_DUT_U (
      .CLK         (CLK),
      .RST       (RESET),
      // -----------------------
      .RX_DATA     (rx_data),
      .RX_META     (),
      .RX_SOF_POS  (rx_sof_pos),
      .RX_EOF_POS  (rx_eof_pos),
      .RX_SOF      (rx_sof),
      .RX_EOF      (rx_eof),
      .RX_SRC_RDY  (rx_src_rdy),
      .RX_DST_RDY  (rx_dst_rdy),
      // -----------------------
      .TX_DATA     (TX.DATA),
      .TX_META     (),
      .TX_SOF_POS  (TX.SOF_POS),
      .TX_EOF_POS  (TX.EOF_POS),
      .TX_SOF      (TX.SOF),
      .TX_EOF      (TX.EOF),
      .TX_SRC_RDY  (TX.SRC_RDY),
      .TX_DST_RDY  (TX.DST_RDY)
   );

endmodule
