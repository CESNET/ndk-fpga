//-- dut.sv: Design under test
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT (
    input logic   CLK,
    input logic   RST,
    mvb_if.dut_rx mvb_rx0,
    mvb_if.dut_rx mvb_rx1,
    mvb_if.dut_tx mvb_tx,
    mvb_if.dut_tx mvb_tx0,
    mvb_if.dut_tx mvb_tx1
);

    logic                   tx_src_rdy_shared;
    logic [RX0_ITEMS-1 : 0] tx_vld_shared;

    assign mvb_tx .SRC_RDY = tx_src_rdy_shared;
    assign mvb_tx0.SRC_RDY = tx_src_rdy_shared;
    assign mvb_tx1.SRC_RDY = tx_src_rdy_shared;

    assign mvb_tx0.DST_RDY = mvb_tx.DST_RDY;
    assign mvb_tx1.DST_RDY = mvb_tx.DST_RDY;

    assign mvb_tx .VLD     = tx_vld_shared;
    assign mvb_tx0.VLD     = tx_vld_shared;
    assign mvb_tx1.VLD     = tx_vld_shared;

    MVB_MERGE_ITEMS #(
        .RX0_ITEMS      (RX0_ITEMS     ),
        .RX0_ITEM_WIDTH (RX0_ITEM_WIDTH),
        .RX1_ITEMS      (RX1_ITEMS     ),
        .RX1_ITEM_WIDTH (RX1_ITEM_WIDTH),
        .TX_ITEM_WIDTH  (TX_ITEM_WIDTH ),
        .RX0_FIFO_EN    (RX0_FIFO_EN   ),
        .FIFO_DEPTH     (FIFO_DEPTH    ),
        .OUTPUT_REG     (OUTPUT_REG    ),
        .DEVICE         (DEVICE        )
    ) VHDL_DUT_U (
        .CLK         (CLK),
        .RESET       (RST),

        .RX0_DATA    (mvb_rx0.DATA   ),
        .RX0_VLD     (mvb_rx0.VLD    ),
        .RX0_SRC_RDY (mvb_rx0.SRC_RDY),
        .RX0_DST_RDY (mvb_rx0.DST_RDY),

        .RX1_DATA    (mvb_rx1.DATA   ),
        .RX1_VLD     (mvb_rx1.VLD    ),
        .RX1_SRC_RDY (mvb_rx1.SRC_RDY),
        .RX1_DST_RDY (mvb_rx1.DST_RDY),

        .TX_DATA     (mvb_tx .DATA     ),
        .TX_DATA0    (mvb_tx0.DATA     ),
        .TX_DATA1    (mvb_tx1.DATA     ),
        .TX_VLD      (tx_vld_shared    ),
        .TX_SRC_RDY  (tx_src_rdy_shared),
        .TX_DST_RDY  (mvb_tx.DST_RDY   )
    );

endmodule
