// dut.sv: Design Under Test
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

module DUT #(int unsigned MVB_ITEMS, int unsigned MVB_ITEM_WIDTH, int unsigned RX_STREAMS, bit RX_SHAKEDOWN_EN, int unsigned SW_TIMEOUT_W, string DEVICE)
(
    input logic CLK,
    input logic RST,
    mvb_if.dut_rx mvb_rx[RX_STREAMS],
    mvb_if.dut_tx mvb_tx
);

    logic [RX_STREAMS*MVB_ITEMS*MVB_ITEM_WIDTH-1 : 0] rx_mvb_data;
    logic [RX_STREAMS*MVB_ITEMS               -1 : 0] rx_mvb_vld;
    logic [RX_STREAMS                         -1 : 0] rx_mvb_src_rdy;
    logic [RX_STREAMS                         -1 : 0] rx_mvb_dst_rdy;

    MVB_MERGE_STREAMS #(
        .MVB_ITEMS       (MVB_ITEMS),
        .MVB_ITEM_WIDTH  (MVB_ITEM_WIDTH),
        .RX_STREAMS      (RX_STREAMS),
        .RX_SHAKEDOWN_EN (RX_SHAKEDOWN_EN),
        .SW_TIMEOUT_W    (SW_TIMEOUT_W),
        .DEVICE          (DEVICE)
    ) VHDL_DUT_U (
        .CLK   (CLK),
        .RESET (RST),

        .RX_DATA    (rx_mvb_data),
        .RX_VLD     (rx_mvb_vld),
        .RX_SRC_RDY (rx_mvb_src_rdy),
        .RX_DST_RDY (rx_mvb_dst_rdy),

        .TX_DATA    (mvb_tx.DATA),
        .TX_VLD     (mvb_tx.VLD),
        .TX_SRC_RDY (mvb_tx.SRC_RDY),
        .TX_DST_RDY (mvb_tx.DST_RDY)
    );

    generate;
        for (genvar i = 0; i < RX_STREAMS; i++) begin
            assign rx_mvb_data[MVB_ITEMS*MVB_ITEM_WIDTH*(i+1)-1 -: MVB_ITEMS*MVB_ITEM_WIDTH] = mvb_rx[i].DATA;
            assign rx_mvb_vld [MVB_ITEMS               *(i+1)-1 -: MVB_ITEMS]                = mvb_rx[i].VLD;
            assign rx_mvb_src_rdy[i] = mvb_rx[i].SRC_RDY;
            assign mvb_rx[i].DST_RDY = rx_mvb_dst_rdy[i];
        end
    endgenerate

endmodule
