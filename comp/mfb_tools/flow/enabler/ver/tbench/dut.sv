/*!
 * \file dut.sv
 * \brief Design Under Test
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2017
 */
 /*
 * Copyright (C) 2017 CESNET z. s. p. o.
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
   iMfbTx.dut TX,
   iMvbRx.dut REG
);

logic reg_enable;
logic [REGIONS-1 : 0] stat_discarded;
logic [32-1 : 0] cnt_discarded;

MFB_ENABLER #(
   .REGIONS     (REGIONS),
   .REGION_SIZE (REGION_SIZE),
   .BLOCK_SIZE  (BLOCK_SIZE),
   .ITEM_WIDTH  (ITEM_WIDTH),
   .META_WIDTH  (0)
) VHDL_DUT_U (
   .CLK            (CLK),
   .RESET          (RESET),
   // RX MFB INTERFACE
   .RX_DATA        (RX.DATA),
   .RX_META        (),
   .RX_SOF_POS     (RX.SOF_POS),
   .RX_EOF_POS     (RX.EOF_POS),
   .RX_SOF         (RX.SOF),
   .RX_EOF         (RX.EOF),
   .RX_SRC_RDY     (RX.SRC_RDY),
   // TX MFB INTERFACE
   .TX_DATA        (TX.DATA),
   .TX_META        (),
   .TX_SOF_POS     (TX.SOF_POS),
   .TX_EOF_POS     (TX.EOF_POS),
   .TX_SOF         (TX.SOF),
   .TX_EOF         (TX.EOF),
   .TX_SRC_RDY     (TX.SRC_RDY),
   .TX_ENABLE      (reg_enable),
   // STATISTICS INCREMENT
   .STAT_DISCARDED (stat_discarded)
);

assign REG.DST_RDY = 1;
assign RX.DST_RDY = 1;
assign reg_enable = REG.DATA[0] || REG.DATA[2];

always @ (posedge CLK)
begin
   if (RESET == 1) begin
      cnt_discarded = 32'h00;
   end else begin
      for (int i = 0; i < REGIONS; i = i +1) begin
         cnt_discarded = cnt_discarded + stat_discarded[i];
      end
   end
end

endmodule
