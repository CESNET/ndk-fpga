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
    iMvbTx.dut TX
);

logic [REGIONS-1:0] tx_eof;
logic tx_src_rdy;

MFB_FRAME_LNG #(
    .REGIONS       (REGIONS),
    .REGION_SIZE   (REGION_SIZE),
    .BLOCK_SIZE    (BLOCK_SIZE),
    .ITEM_WIDTH    (ITEM_WIDTH),
    .LNG_WIDTH     (LNG_WIDTH),
    .SATURATION    (SATURATION)
) VHDL_DUT_U (
    .CLK           (CLK),
    .RESET         (RESET),
    // RX MFB INTERFACE
    .RX_DATA       (RX.DATA),
    .RX_SOF_POS    (RX.SOF_POS),
    .RX_EOF_POS    (RX.EOF_POS),
    .RX_SOF        (RX.SOF),
    .RX_EOF        (RX.EOF),
    .RX_SRC_RDY    (RX.SRC_RDY),
    .RX_DST_RDY    (RX.DST_RDY),
    // TX MFB INTERFACE
    .TX_DATA       (),
    .TX_SOF_POS    (),
    .TX_EOF_POS    (),
    .TX_SOF        (),
    .TX_EOF        (tx_eof),
    .TX_TEMP_LNG   (),
    .TX_FRAME_LNG  (TX.DATA),
    .TX_SRC_RDY    (tx_src_rdy),
    .TX_DST_RDY    (TX.DST_RDY)
);

assign TX.VLD = tx_eof;
assign TX.SRC_RDY = (|tx_eof) && tx_src_rdy;

endmodule
