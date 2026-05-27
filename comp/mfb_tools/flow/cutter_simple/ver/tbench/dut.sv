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
import math_pkg::*;

module DUT (
   input logic CLK,
   input logic RESET,
   iMfbRx.dut RX,
   iMfbTx.dut TX
);

localparam int CUT_OFFSET_WIDTH = ($clog2(MAX_CUT_OFFSET) > 1) ? $clog2(MAX_CUT_OFFSET) : 1;

logic [REGIONS-1 : 0]                  cut;
logic [REGIONS*CUT_OFFSET_WIDTH-1 : 0] cut_off;

generate
   for (genvar r = 0; r < REGIONS; r++) begin : meta_to_cut_g
      if (MAX_CUT_OFFSET == 0) begin : max_cut_off_0_g
         assign cut_off[r] = 0;
         assign cut[r] = RX.META[2*r];
      end else if (MAX_CUT_OFFSET == 1) begin : max_cut_off_1_g
         assign cut_off[r] = RX.META[2*r+1];
         assign cut[r] = RX.META[2*r];
      end else begin : max_cut_off_more_g
         assign cut_off[(r+1)*$clog2(MAX_CUT_OFFSET)-1 : r*$clog2(MAX_CUT_OFFSET)]
            = RX.META[(r+1)*($clog2(MAX_CUT_OFFSET)+1)+1-1 : r*($clog2(MAX_CUT_OFFSET)+1)+1];
         assign cut[r] = RX.META[r*($clog2(MAX_CUT_OFFSET)+1)];
      end
   end
endgenerate


MFB_CUTTER_SIMPLE #(
   .REGIONS       (REGIONS),
   .REGION_SIZE   (REGION_SIZE),
   .BLOCK_SIZE    (BLOCK_SIZE),
   .ITEM_WIDTH    (ITEM_WIDTH),
   .CUTTED_ITEMS  (CUTTED_ITEMS),
   .MAX_CUT_OFFSET(MAX_CUT_OFFSET)
) VHDL_DUT_U (
   .CLK        (CLK),
   .RESET      (RESET),
   // RX MFB INTERFACE
   .RX_DATA    (RX.DATA),
   .RX_SOF_POS (RX.SOF_POS),
   .RX_EOF_POS (RX.EOF_POS),
   .RX_SOF     (RX.SOF),
   .RX_EOF     (RX.EOF),
   .RX_SRC_RDY (RX.SRC_RDY),
   .RX_DST_RDY (RX.DST_RDY),
   .RX_CUT     (cut),
   .RX_CUT_OFF (cut_off),
   // TX MFB INTERFACE
   .TX_DATA    (TX.DATA),
   .TX_SOF_POS (TX.SOF_POS),
   .TX_EOF_POS (TX.EOF_POS),
   .TX_SOF     (TX.SOF),
   .TX_EOF     (TX.EOF),
   .TX_SRC_RDY (TX.SRC_RDY),
   .TX_DST_RDY (TX.DST_RDY)
);

endmodule
