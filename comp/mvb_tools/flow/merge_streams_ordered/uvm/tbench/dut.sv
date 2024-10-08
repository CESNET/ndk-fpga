// dut.sv: Design under test
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT (
    input logic   CLK,
    input logic   RST,
    mvb_if.dut_rx rx_mvb [RX_STREAMS -1 : 0],
    mvb_if.dut_rx rx_sel_mvb,
    mvb_if.dut_tx tx_mvb
);

    logic [MVB_ITEMS*MVB_ITEM_WIDTH -1 : 0] rx_mvb_data [RX_STREAMS -1 : 0];
    logic [MVB_ITEMS -1 : 0]                rx_mvb_vld  [RX_STREAMS -1 : 0];
    logic [RX_STREAMS -1 : 0]               rx_mvb_src_rdy;
    logic [RX_STREAMS -1 : 0]               rx_mvb_dst_rdy;

    for (genvar port = 0; port < RX_STREAMS; port++) begin
        assign rx_mvb_data[port]    = rx_mvb[port].DATA;
        assign rx_mvb_vld[port]     = rx_mvb[port].VLD;
        assign rx_mvb_src_rdy[port] = rx_mvb[port].SRC_RDY;
        assign rx_mvb[port].DST_RDY = rx_mvb_dst_rdy[port] ;
    end

    MVB_MERGE_STREAMS_ORDERED #(
        .MVB_ITEMS          (MVB_ITEMS),
        .MVB_ITEM_WIDTH     (MVB_ITEM_WIDTH),
        .RX_STREAMS         (RX_STREAMS),
        .USE_FIFOX_MULTI    (USE_FIFOX_MULTI),
        .FIFOX_ITEMS_MULT   (FIFOX_ITEMS_MULT),
        .SEL_SHAKEDOWN_EN   (SEL_SHAKEDOWN_EN),
        .DEVICE             (DEVICE)
    ) VHDL_DUT_U (
        .CLK            (CLK),
        .RESET          (RST),

        .RX_DATA        (rx_mvb_data),
        .RX_VLD         (rx_mvb_vld),
        .RX_SRC_RDY     (rx_mvb_src_rdy),
        .RX_DST_RDY     (rx_mvb_dst_rdy),

        .RX_SEL_IF      (rx_sel_mvb.DATA),
        .RX_SEL_VLD     (rx_sel_mvb.VLD),
        .RX_SEL_SRC_RDY (rx_sel_mvb.SRC_RDY),
        .RX_SEL_DST_RDY (rx_sel_mvb.DST_RDY),

        .TX_DATA        (tx_mvb.DATA),
        .TX_VLD         (tx_mvb.VLD),
        .TX_SRC_RDY     (tx_mvb.SRC_RDY),
        .TX_DST_RDY     (tx_mvb.DST_RDY)
    );
endmodule
