//-- dut.sv: Design under test
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT (
    input logic     CLK,
    reset_if        reset,
    mfb_if.dut_rx   mfb_rx,
    mfb_if.dut_tx   mfb_tx[SPLITTER_OUTPUTS]
    );

    localparam ITEM_WIDTH = 8;
    localparam DATA_WIDTH = REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH;
    localparam META_FOR_ONE_OUTPUT_WIDTH = REGIONS*META_WIDTH;
    localparam SOF_POS_WIDTH = REGIONS*$clog2(REGION_SIZE);
    localparam EOF_POS_WIDTH = REGIONS*$clog2(REGION_SIZE*BLOCK_SIZE);

    logic [DATA_WIDTH -1:0]                 tx_mfb_data     [SPLITTER_OUTPUTS-1:0];
    logic [META_FOR_ONE_OUTPUT_WIDTH-1:0]   tx_mfb_meta     [SPLITTER_OUTPUTS-1:0];
    logic [REGIONS -1:0]                    tx_mfb_sof      [SPLITTER_OUTPUTS-1:0];
    logic [REGIONS -1:0]                    tx_mfb_eof      [SPLITTER_OUTPUTS-1:0];
    logic [SOF_POS_WIDTH -1:0]              tx_mfb_sof_pos  [SPLITTER_OUTPUTS-1:0];
    logic [EOF_POS_WIDTH -1:0]              tx_mfb_eof_pos  [SPLITTER_OUTPUTS-1:0];
    logic [SPLITTER_OUTPUTS-1:0]            tx_mfb_src_rdy;
    logic [SPLITTER_OUTPUTS-1:0]            tx_mfb_dst_rdy;

    logic [REGIONS*META_WIDTH -1:0]               rx_mfb_meta;
    logic [REGIONS*$clog2(SPLITTER_OUTPUTS) -1:0] rx_mfb_sel;

    generate
        for (genvar i = 0; i< SPLITTER_OUTPUTS; i++) begin
            assign mfb_tx[i].DATA    = tx_mfb_data[i];
            assign mfb_tx[i].META    = tx_mfb_meta[i];
            assign mfb_tx[i].SOF     = tx_mfb_sof[i];
            assign mfb_tx[i].EOF     = tx_mfb_eof[i];
            assign mfb_tx[i].SOF_POS = tx_mfb_sof_pos[i];
            assign mfb_tx[i].EOF_POS = tx_mfb_eof_pos[i];
            assign mfb_tx[i].SRC_RDY = tx_mfb_src_rdy[i];
            assign tx_mfb_dst_rdy[i] = mfb_tx [i].DST_RDY;
        end

        for (genvar it = 0; it < REGIONS; it++) begin
            assign rx_mfb_meta[(it+1)*META_WIDTH-1 -: META_WIDTH]                             = mfb_rx.META[it*(META_WIDTH +$clog2(SPLITTER_OUTPUTS)) +META_WIDTH -1                           -: META_WIDTH];
            assign rx_mfb_sel [(it+1)*$clog2(SPLITTER_OUTPUTS)-1 -: $clog2(SPLITTER_OUTPUTS)] = mfb_rx.META[it*(META_WIDTH +$clog2(SPLITTER_OUTPUTS)) +META_WIDTH +$clog2(SPLITTER_OUTPUTS) -1 -: $clog2(SPLITTER_OUTPUTS)];
        end
    endgenerate

    MFB_SPLITTER_SIMPLE_GEN #(
        .SPLITTER_OUTPUTS   (SPLITTER_OUTPUTS),
        .REGIONS            (REGIONS),
        .REGION_SIZE        (REGION_SIZE),
        .BLOCK_SIZE         (BLOCK_SIZE),
        .ITEM_WIDTH         (ITEM_WIDTH),
        .META_WIDTH         (META_WIDTH),
        .DEVICE             (DEVICE)
    ) VHDL_DUT_U (
        .CLK                (CLK),
        .RESET              (reset.RESET),
        .RX_MFB_SEL         (rx_mfb_sel),
        .RX_MFB_DATA        (mfb_rx.DATA),
        .RX_MFB_META        (rx_mfb_meta),
        .RX_MFB_SOF_POS     (mfb_rx.SOF_POS),
        .RX_MFB_EOF_POS     (mfb_rx.EOF_POS),
        .RX_MFB_SOF         (mfb_rx.SOF),
        .RX_MFB_EOF         (mfb_rx.EOF),
        .RX_MFB_SRC_RDY     (mfb_rx.SRC_RDY),
        .RX_MFB_DST_RDY     (mfb_rx.DST_RDY),
        .TX_MFB_DATA        (tx_mfb_data),
        .TX_MFB_META        (tx_mfb_meta),
        .TX_MFB_SOF_POS     (tx_mfb_sof_pos),
        .TX_MFB_EOF_POS     (tx_mfb_eof_pos),
        .TX_MFB_SOF         (tx_mfb_sof),
        .TX_MFB_EOF         (tx_mfb_eof),
        .TX_MFB_SRC_RDY     (tx_mfb_src_rdy),
        .TX_MFB_DST_RDY     (tx_mfb_dst_rdy)
    );


endmodule
