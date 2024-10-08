/*!
 * \file dut.sv
 * \brief Design Under Test
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2017
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
   iMfbTx.dut TX,
   iMvbTx.dut EX
);

MFB_GET_ITEMS #(
   .REGIONS          (REGIONS),
   .REGION_SIZE      (REGION_SIZE),
   .BLOCK_SIZE       (BLOCK_SIZE),
   .ITEM_WIDTH       (ITEM_WIDTH),
   .MAX_FRAME_LENGHT (((FRAME_SIZE_MAX*ITEM_WIDTH)/8)),
   .EXTRACTED_ITEMS  (EXTRACTED_ITEMS),
   .EXTRACTED_OFFSET (EXTRACTED_OFFSET)
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
   // TX MFB INTERFACE
   .TX_DATA    (TX.DATA),
   .TX_SOF_POS (TX.SOF_POS),
   .TX_EOF_POS (TX.EOF_POS),
   .TX_SOF     (TX.SOF),
   .TX_EOF     (TX.EOF),
   .TX_SRC_RDY (TX.SRC_RDY),
   .TX_DST_RDY (TX.DST_RDY),
   // EX MVB INTERFACE WITHOUT DST RDY
   .EX_DATA    (EX.DATA),
   .EX_VLD     (EX.VLD),
   .EX_SRC_RDY (EX.SRC_RDY),
   .EX_DST_RDY (EX.DST_RDY)
);

endmodule
