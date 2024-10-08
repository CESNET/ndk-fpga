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
    iMvbRx.dut RX_MVB[MERGER_INPUTS-1:0],
    iMfbRx.dut RX_MFB[MERGER_INPUTS-1:0],
    iMvbTx.dut TX_MVB,
    iMfbTx.dut TX_MFB
);

    localparam SOF_WIDTH = math_pkg::max(1,$clog2(MFB_REG_SIZE));
    localparam EOF_WIDTH = math_pkg::max(1,$clog2(MFB_REG_SIZE*MFB_BLOCK_SIZE));

    logic [MERGER_INPUTS-1:0] [MVB_ITEMS*MVB_ITEM_WIDTH-1:0] rx_mvb_data   ;
    logic [MERGER_INPUTS-1:0] [MVB_ITEMS               -1:0] rx_mvb_payload;
    logic [MERGER_INPUTS-1:0] [MVB_ITEMS               -1:0] rx_mvb_vld    ;
    logic [MERGER_INPUTS-1:0]                                rx_mvb_src_rdy;
    logic [MERGER_INPUTS-1:0]                                rx_mvb_dst_rdy;

    logic [MERGER_INPUTS-1:0] [MFB_REGIONS*MFB_REG_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1:0] rx_mfb_data   ;
    logic [MERGER_INPUTS-1:0] [MFB_REGIONS*MFB_META_WIDTH                            -1:0] rx_mfb_meta   ;
    logic [MERGER_INPUTS-1:0] [MFB_REGIONS                                           -1:0] rx_mfb_sof    ;
    logic [MERGER_INPUTS-1:0] [MFB_REGIONS                                           -1:0] rx_mfb_eof    ;
    logic [MERGER_INPUTS-1:0] [MFB_REGIONS*SOF_WIDTH                                 -1:0] rx_mfb_sof_pos;
    logic [MERGER_INPUTS-1:0] [MFB_REGIONS*EOF_WIDTH                                 -1:0] rx_mfb_eof_pos;
    logic [MERGER_INPUTS-1:0]                                                              rx_mfb_src_rdy;
    logic [MERGER_INPUTS-1:0]                                                              rx_mfb_dst_rdy;

    logic [MVB_ITEMS*MVB_ITEM_WIDTH-1:0] tx_mvb_data   ;
    logic [MVB_ITEMS               -1:0] tx_mvb_payload;

    generate
        for (genvar i = 0; i < MERGER_INPUTS; i++) begin

            for (genvar e = 0; e < MVB_ITEMS; e++) begin
                assign rx_mvb_data   [i][(e+1)*MVB_ITEM_WIDTH-1 : e*MVB_ITEM_WIDTH] = RX_MVB[i].DATA[(e+1)*MVB_ITEM_WIDTH-1 : e*MVB_ITEM_WIDTH];
                assign rx_mvb_payload[i][e]                                         = RX_MVB[i].DATA[e*MVB_ITEM_WIDTH];
            end
            assign rx_mvb_vld    [i] = RX_MVB[i].VLD    ;
            assign rx_mvb_src_rdy[i] = RX_MVB[i].SRC_RDY;
            assign RX_MVB[i].DST_RDY = rx_mvb_dst_rdy[i];

            assign rx_mfb_data   [i] = RX_MFB[i].DATA   ;
            assign rx_mfb_meta   [i] = RX_MFB[i].META   ;
            assign rx_mfb_sof    [i] = RX_MFB[i].SOF    ;
            assign rx_mfb_eof    [i] = RX_MFB[i].EOF    ;
            assign rx_mfb_sof_pos[i] = RX_MFB[i].SOF_POS;
            assign rx_mfb_eof_pos[i] = RX_MFB[i].EOF_POS;
            assign rx_mfb_src_rdy[i] = RX_MFB[i].SRC_RDY;
            assign RX_MFB[i].DST_RDY = rx_mfb_dst_rdy[i];

        end

        for (genvar e = 0; e < MVB_ITEMS; e++) begin
            assign TX_MVB.DATA[(e+1)*MVB_ITEM_WIDTH-1 : e*MVB_ITEM_WIDTH+1] = tx_mvb_data[(e+1)*MVB_ITEM_WIDTH-1 : e*MVB_ITEM_WIDTH+1];
            assign TX_MVB.DATA[e*MVB_ITEM_WIDTH]                            = tx_mvb_payload[e];
        end

    endgenerate

    DUT_WRAPPER #(
        .MERGER_INPUTS   (MERGER_INPUTS  ),
        .MVB_ITEMS       (MVB_ITEMS      ),
        .MVB_ITEM_WIDTH  (MVB_ITEM_WIDTH ),
        .MFB_REGIONS     (MFB_REGIONS    ),
        .MFB_REG_SIZE    (MFB_REG_SIZE   ),
        .MFB_BLOCK_SIZE  (MFB_BLOCK_SIZE ),
        .MFB_ITEM_WIDTH  (MFB_ITEM_WIDTH ),
        .MFB_META_WIDTH  (MFB_META_WIDTH ),
        .INPUT_FIFO_SIZE (INPUT_FIFO_SIZE),
        .RX_PAYLOAD_EN   (RX_PAYLOAD_EN  ),
        .IN_PIPE_EN      (IN_PIPE_EN     ),
        .OUT_PIPE_EN     (OUT_PIPE_EN    ),
        .DEVICE          (DEVICE         )
    ) VHDL_DUT_U (
        .CLK            (CLK  ),
        .RESET          (RESET),

        .RX_MVB_DATA    (rx_mvb_data   ),
        .RX_MVB_PAYLOAD (rx_mvb_payload),
        .RX_MVB_VLD     (rx_mvb_vld    ),
        .RX_MVB_SRC_RDY (rx_mvb_src_rdy),
        .RX_MVB_DST_RDY (rx_mvb_dst_rdy),

        .RX_MFB_DATA    (rx_mfb_data   ),
        .RX_MFB_META    (rx_mfb_meta   ),
        .RX_MFB_SOF     (rx_mfb_sof    ),
        .RX_MFB_EOF     (rx_mfb_eof    ),
        .RX_MFB_SOF_POS (rx_mfb_sof_pos),
        .RX_MFB_EOF_POS (rx_mfb_eof_pos),
        .RX_MFB_SRC_RDY (rx_mfb_src_rdy),
        .RX_MFB_DST_RDY (rx_mfb_dst_rdy),

        .TX_MVB_DATA    (tx_mvb_data   ),
        .TX_MVB_PAYLOAD (tx_mvb_payload),
        .TX_MVB_VLD     (TX_MVB.VLD    ),
        .TX_MVB_SRC_RDY (TX_MVB.SRC_RDY),
        .TX_MVB_DST_RDY (TX_MVB.DST_RDY),

        .TX_MFB_DATA    (TX_MFB.DATA   ),
        .TX_MFB_META    (TX_MFB.META   ),
        .TX_MFB_SOF     (TX_MFB.SOF    ),
        .TX_MFB_EOF     (TX_MFB.EOF    ),
        .TX_MFB_SOF_POS (TX_MFB.SOF_POS),
        .TX_MFB_EOF_POS (TX_MFB.EOF_POS),
        .TX_MFB_SRC_RDY (TX_MFB.SRC_RDY),
        .TX_MFB_DST_RDY (TX_MFB.DST_RDY)
    );

endmodule
