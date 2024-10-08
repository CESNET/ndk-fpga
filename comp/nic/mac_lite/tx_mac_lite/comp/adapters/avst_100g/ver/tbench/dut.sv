/*!
 * \file dut.sv
 * \brief Design Under Test
 * \author Michal Szabo <xszabo11@vutbr.cz>
 * \date 2018
 */
 /*
 * Copyright (C) 2017 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import math_pkg::*;
import test_pkg::*;

module DUT (
    input logic CLK,
    input logic RESET,
    iMfbRx.dut RX,
    iMfbTx.dut TX
);

    localparam EMPTY_WIDTH = log2(DATA_WIDTH/8);

    logic [DATA_WIDTH-1 : 0]  tx_avst_data;
    logic [DATA_WIDTH-1 : 0]  tx_mfb_data;
    logic [EMPTY_WIDTH-1 : 0] tx_avst_empty;
    logic [EMPTY_WIDTH-1 : 0] tx_mfb_eof_pos;

    TX_MAC_LITE_ADAPTER_AVST_100G #(
        .DATA_WIDTH  (DATA_WIDTH),
        .FIFO_DEPTH  (FIFO_DEPTH)
    ) VHDL_DUT_U (
        .CLK         (CLK),
        .RESET       (RESET),

        .RX_MFB_DATA    (RX.DATA),
        .RX_MFB_SOF_POS (RX.SOF_POS),
        .RX_MFB_EOF_POS (RX.EOF_POS),
        .RX_MFB_SOF     (RX.SOF),
        .RX_MFB_EOF     (RX.EOF),
        .RX_MFB_SRC_RDY (RX.SRC_RDY),
        .RX_MFB_DST_RDY (RX.DST_RDY),

        .TX_AVST_DATA  (tx_avst_data),
        .TX_AVST_SOP   (TX.SOF),
        .TX_AVST_EOP   (TX.EOF),
        .TX_AVST_EMPTY (tx_avst_empty),
        .TX_AVST_ERROR (),
        .TX_AVST_VALID (TX.SRC_RDY),
        .TX_AVST_READY (TX.DST_RDY)
    );

    genvar i;
    for (i=0; i<(DATA_WIDTH/8); i=i+1) begin
        assign tx_mfb_data[(i*8) +:8] = tx_avst_data[(((DATA_WIDTH/8)-1-i)*8) +:8];
    end

    assign tx_mfb_eof_pos = ~tx_avst_empty;
    assign TX.EOF_POS = tx_mfb_eof_pos;
    assign TX.DATA = tx_mfb_data;

endmodule
