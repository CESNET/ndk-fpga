// dut.sv: Design under test
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kriz <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


import test::*;

module DUT (
    input logic     CLK,
    input logic     RST,
    mfb_if.dut_rx   mfb_rx,
    mvb_if.dut_tx   mvb_tx,
    mvb_if.dut_tx   mvb_end
    );

    logic [MFB_REGIONS*OFFSET_WIDTH-1 : 0] offset;
    logic [MFB_REGIONS*LENGTH_WIDTH-1 : 0] length;
    logic [MFB_REGIONS-1 : 0]              rx_en;
    logic                                  mvb_src_rdy;

    generate
        for (genvar r = 0; r < MFB_REGIONS; r++) begin
            assign offset  [(r+1)*OFFSET_WIDTH-1 : r*OFFSET_WIDTH] = mfb_rx.META[(r*META_WIDTH)+OFFSET_WIDTH-1              : r*META_WIDTH];
            assign length  [(r+1)*LENGTH_WIDTH-1 : r*LENGTH_WIDTH] = mfb_rx.META[(r*META_WIDTH)+OFFSET_WIDTH+LENGTH_WIDTH-1 : OFFSET_WIDTH+(r*META_WIDTH)];
            assign rx_en[r]                                        = mfb_rx.META[(r*META_WIDTH)+META_WIDTH-1                : OFFSET_WIDTH+LENGTH_WIDTH+(r*META_WIDTH)];
        end
    endgenerate

    logic [((MFB_REGION_SIZE != 1) ? MFB_REGIONS*$clog2(MFB_REGION_SIZE) : MFB_REGIONS)-1 : 0] sof_pos;
    generate
        if (MFB_REGION_SIZE != 1) begin
            assign sof_pos = mfb_rx.SOF_POS;
        end else
            assign sof_pos = '0;
    endgenerate

    assign mvb_tx.SRC_RDY  = mvb_src_rdy;

    assign mvb_end.SRC_RDY = mvb_src_rdy;
    assign mvb_end.DST_RDY = mvb_tx.DST_RDY;
    assign mvb_end.VLD     = mvb_tx.VLD;

    MFB_ITEMS_VLD #(
        .MFB_REGIONS     (MFB_REGIONS),
        .MFB_REGION_SIZE (MFB_REGION_SIZE),
        .MFB_BLOCK_SIZE  (MFB_BLOCK_SIZE),
        .MFB_ITEM_WIDTH  (MFB_ITEM_WIDTH),

        .PKT_MTU         (PKT_MTU),
        .OFFSET_WIDTH    (OFFSET_WIDTH),
        .LENGTH_WIDTH    (LENGTH_WIDTH)
    ) VHDL_DUT_U (
        .CLK                (CLK),
        .RESET              (RST),

        .RX_MFB_DATA    (mfb_rx.DATA),
        // TODO
        .RX_MFB_META    (),
        .RX_MFB_SOF_POS (sof_pos),
        .RX_MFB_EOF_POS (mfb_rx.EOF_POS),
        .RX_MFB_SOF     (mfb_rx.SOF),
        .RX_MFB_EOF     (mfb_rx.EOF),
        .RX_MFB_SRC_RDY (mfb_rx.SRC_RDY),
        .RX_MFB_DST_RDY (mfb_rx.DST_RDY),

        .RX_OFFSET      (offset),
        .RX_LENGTH      (length),
        .RX_ENABLE      (rx_en),

        .TX_DATA        (mvb_tx.DATA),
        // TODO
        .TX_META        (),
        .TX_END         (mvb_end.DATA),
        .TX_VLD         (mvb_tx.VLD),
        .TX_SRC_RDY     (mvb_src_rdy),
        .TX_DST_RDY     (mvb_tx.DST_RDY)

    );


endmodule
