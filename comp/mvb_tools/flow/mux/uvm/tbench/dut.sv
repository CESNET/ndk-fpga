//-- dut.sv: Design under test
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Oliver Gurka <xgurka00@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT (
    input logic     CLK,
    input logic     RST,
    mvb_if.dut_rx   mvb_wr [RX_MVB_CNT - 1 : 0],
    mvb_if.dut_rx   mvb_sel,
    mvb_if.dut_tx   mvb_rd
    );

    logic [RX_MVB_CNT * ITEMS * ITEM_WIDTH - 1 : 0]         rx_mvb_data;
    logic [RX_MVB_CNT * ITEMS - 1 : 0]                      rx_mvb_vld;
    logic [RX_MVB_CNT - 1 : 0]                              rx_mvb_src_rdy;
    logic [RX_MVB_CNT - 1 : 0]                              rx_mvb_dst_rdy;

    for (genvar it = 0; it < RX_MVB_CNT; it++) begin
        assign rx_mvb_data[(it+1) * ITEMS * ITEM_WIDTH - 1 -: ITEMS * ITEM_WIDTH] = mvb_wr[it].DATA;
        assign rx_mvb_vld[(it+1) * ITEMS - 1 -: ITEMS] = mvb_wr[it].VLD;
        assign rx_mvb_src_rdy[it] = mvb_wr[it].SRC_RDY;
        assign mvb_wr[it].DST_RDY = rx_mvb_dst_rdy[it];
    end

    GEN_MVB_MUX #(
        .MVB_ITEMS       (ITEMS),
        .DATA_WIDTH  (ITEM_WIDTH),
        .MUX_WIDTH (RX_MVB_CNT)
    ) VHDL_DUT_U (
        .CLK        (CLK),
        .RESET      (RST),

        .RX_DATA    (rx_mvb_data),
        .RX_VLD     (rx_mvb_vld),
        .RX_SRC_RDY (rx_mvb_src_rdy),
        .RX_DST_RDY (rx_mvb_dst_rdy),

        .TX_DATA    (mvb_rd.DATA),
        .TX_VLD     (mvb_rd.VLD),
        .TX_SRC_RDY (mvb_rd.SRC_RDY),
        .TX_DST_RDY (mvb_rd.DST_RDY),

        .RX_SEL_DATA    (mvb_sel.DATA),
        .RX_SEL_VLD     (mvb_sel.VLD),
        .RX_SEL_SRC_RDY (mvb_sel.SRC_RDY),
        .RX_SEL_DST_RDY (mvb_sel.DST_RDY)
    );


endmodule
