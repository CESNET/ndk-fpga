// dut.sv: Design Under Test
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

module DUT #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, LEN_WIDTH, DEVICE)
(
    input logic CLK,
    input logic RST,
    mfb_if.dut_rx mfb_rx,
    mfb_if.dut_tx mfb_tx
);

    logic [REGIONS*LEN_WIDTH -1 : 0] mfb_rx_trim_len;
    logic [REGIONS           -1 : 0] mfb_rx_trim_en;
    logic [REGIONS*META_WIDTH-1 : 0] mfb_rx_meta;

    MFB_FRAME_TRIMMER  #(
        .REGIONS     (REGIONS),
        .REGION_SIZE (REGION_SIZE),
        .BLOCK_SIZE  (BLOCK_SIZE),
        .ITEM_WIDTH  (ITEM_WIDTH),
        .META_WIDTH  (META_WIDTH),
        .LEN_WIDTH   (LEN_WIDTH),
        .DEVICE      (DEVICE)
    ) VHDL_DUT_U (
        .CLK   (CLK),
        .RESET (RST),

        .RX_TRIM_EN  (mfb_rx_trim_en),
        .RX_TRIM_LEN (mfb_rx_trim_len),

        .RX_DATA    (mfb_rx.DATA),
        .RX_META    (mfb_rx_meta),
        .RX_SOF_POS (mfb_rx.SOF_POS),
        .RX_EOF_POS (mfb_rx.EOF_POS),
        .RX_SOF     (mfb_rx.SOF),
        .RX_EOF     (mfb_rx.EOF),

        .RX_SRC_RDY (mfb_rx.SRC_RDY),
        .RX_DST_RDY (mfb_rx.DST_RDY),

        .TX_DATA    (mfb_tx.DATA),
        .TX_META    (mfb_tx.META),
        .TX_SOF_POS (mfb_tx.SOF_POS),
        .TX_EOF_POS (mfb_tx.EOF_POS),
        .TX_SOF     (mfb_tx.SOF),
        .TX_EOF     (mfb_tx.EOF),

        .TX_SRC_RDY (mfb_tx.SRC_RDY),
        .TX_DST_RDY (mfb_tx.DST_RDY)
    );

    generate;
        for (genvar i = 0; i < REGIONS; i++) begin
            logic [META_WIDTH+1+LEN_WIDTH-1 : 0] mfb_rx_meta_slice;

            assign mfb_rx_meta_slice = mfb_rx.META[(META_WIDTH+1+LEN_WIDTH)*(i+1)-1 -: META_WIDTH+1+LEN_WIDTH];

            assign mfb_rx_trim_len[LEN_WIDTH*(i+1)-1 -: LEN_WIDTH]   = mfb_rx_meta_slice[LEN_WIDTH             -1 -: LEN_WIDTH];
            assign mfb_rx_trim_en [i]                                = mfb_rx_meta_slice[1+LEN_WIDTH           -1 -: 1];
            assign mfb_rx_meta    [META_WIDTH*(i+1)-1 -: META_WIDTH] = mfb_rx_meta_slice[META_WIDTH+1+LEN_WIDTH-1 -: META_WIDTH];
        end
    endgenerate

endmodule
