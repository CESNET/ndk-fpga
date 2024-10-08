/*!
 * \file dut.sv
 * \brief Design Under Test
 * \author Daniel Kriz <xkrizd01@vutbr.cz>
 * \date 2020
 */
 /*
 * Copyright (C) 2020 CESNET z. s. p. o.
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
    output logic[CNT_WIDTH-1 : 0] FRAME_COUNTER,
    input logic FRAME_COUNTER_RST,
    iMfbRx.dut RX,
    iMfbTx.dut TX
);

MFB_FRAME_CNT #(
    // MFB charakteristics
    .REGIONS        (REGIONS),
    .REGION_SIZE    (REGION_SIZE),
    .BLOCK_SIZE     (BLOCK_SIZE),
    .ITEM_WIDTH     (ITEM_WIDTH),
    //Others
    .OUTPUT_REG     (OUTPUT_REG),
    .CNT_WIDTH      (CNT_WIDTH),
    .AUTO_RESET     (AUTO_RESET),
    .IMPLEMENTATION (IMPLEMENTATION)
) VHDL_DUT_U (
    .CLK           (CLK),
    .RST           (RESET),
    // RX MFB INTERFACE
    .RX_DATA       (RX.DATA),
    .RX_SOF_POS    (RX.SOF_POS),
    .RX_EOF_POS    (RX.EOF_POS),
    .RX_SOF        (RX.SOF),
    .RX_EOF        (RX.EOF),
    .RX_SRC_RDY    (RX.SRC_RDY),
    .RX_DST_RDY    (RX.DST_RDY),
    // TX MFB INTERFACE
    .TX_DATA       (TX.DATA),
    .TX_FRAME_NUM  (TX.META),
    .TX_SOF_POS    (TX.SOF_POS),
    .TX_EOF_POS    (TX.EOF_POS),
    .TX_SOF        (TX.SOF),
    .TX_EOF        (TX.EOF),
    .TX_SRC_RDY    (TX.SRC_RDY),
    .TX_DST_RDY    (TX.DST_RDY),
    // TOTAL FRAME COUNTER
    .FRAME_CNT     (FRAME_COUNTER),
    .FRAME_CNT_RST (FRAME_COUNTER_RST)
);

endmodule
