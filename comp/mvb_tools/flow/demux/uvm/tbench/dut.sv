// dut.sv: Design under test
// Copyright (C) 2022-2024 CESNET z.s.p.o.
// Author: Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
//         Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT (
    input logic     CLK,
    input logic     RST,
    mvb_if.dut_rx   rx_mvb,
    mvb_if.dut_tx   tx_mvb [TX_PORTS -1 : 0]
    );

    localparam int unsigned SEL_WIDTH         = $clog2(TX_PORTS);
    localparam int unsigned TOTAL_ITEM_WIDTH  = ITEM_WIDTH + SEL_WIDTH;

    logic [ITEMS*ITEM_WIDTH -1 : 0]               RX_DATA;
    logic [ITEMS*$clog2(TX_PORTS) -1 : 0]         RX_SEL;

    logic [TX_PORTS * ITEMS * ITEM_WIDTH -1 : 0]  tx_mvb_data;
    logic [TX_PORTS * ITEMS -1 : 0]               tx_mvb_vld;
    logic [TX_PORTS -1 : 0]                       tx_mvb_src_rdy;
    logic [TX_PORTS -1 : 0]                       tx_mvb_dst_rdy;

    for (genvar it = 0; it < ITEMS; it++) begin
        assign RX_DATA[(it+1) * ITEM_WIDTH -1 -: ITEM_WIDTH] = rx_mvb.DATA[it * TOTAL_ITEM_WIDTH + ITEM_WIDTH -1 -: ITEM_WIDTH];
        assign RX_SEL[(it+1) * SEL_WIDTH -1 -: SEL_WIDTH]    = rx_mvb.DATA[(it+1) * TOTAL_ITEM_WIDTH -1 -: SEL_WIDTH];
    end

    for (genvar it = 0; it < TX_PORTS; it++) begin
        assign tx_mvb[it].DATA    = tx_mvb_data[(it+1) * ITEMS * ITEM_WIDTH -1 -: ITEMS * ITEM_WIDTH];
        assign tx_mvb[it].VLD     = tx_mvb_vld[(it+1) * ITEMS -1 -: ITEMS];
        assign tx_mvb[it].SRC_RDY = tx_mvb_src_rdy[it];
        assign tx_mvb_dst_rdy[it] = tx_mvb[it].DST_RDY;
    end

    GEN_MVB_DEMUX #(
        .MVB_ITEMS   (ITEMS),
        .DATA_WIDTH  (ITEM_WIDTH),
        .DEMUX_WIDTH (TX_PORTS),
        .VERSION     (DEMUX_VERSION),
        .OUTPUT_REG  (OUTPUT_REG_EN)
    ) VHDL_DUT_U (
        .CLK        (CLK),
        .RESET      (RST),

        .RX_DATA    (RX_DATA),
        .RX_SEL     (RX_SEL),
        .RX_VLD     (rx_mvb.VLD),
        .RX_SRC_RDY (rx_mvb.SRC_RDY),
        .RX_DST_RDY (rx_mvb.DST_RDY),

        .TX_DATA    (tx_mvb_data),
        .TX_VLD     (tx_mvb_vld),
        .TX_SRC_RDY (tx_mvb_src_rdy),
        .TX_DST_RDY (tx_mvb_dst_rdy)
    );
endmodule
