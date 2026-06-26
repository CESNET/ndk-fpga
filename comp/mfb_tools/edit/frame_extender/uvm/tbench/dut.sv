// dut.sv: Design Under Test
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

module DUT #(
    int unsigned MFB_REGIONS,
    int unsigned MFB_REGION_SIZE,
    int unsigned MFB_BLOCK_SIZE,
    int unsigned MFB_ITEM_WIDTH,
    int unsigned PKT_MTU,
    int unsigned MVB_FIFO_DEPTH,
    int unsigned MFB_FIFO_DEPTH,
    int unsigned USERMETA_WIDTH,
    string       DEVICE,
    int unsigned RX_MVB_ITEM_WIDTH
)
(
    input logic CLK,
    input logic RST,
    mfb_if.dut_rx mfb_rx,
    mvb_if.dut_rx mvb_rx,
    mfb_if.dut_tx mfb_tx,
    mvb_if.dut_tx mvb_tx
);

    logic [MFB_REGIONS*USERMETA_WIDTH   -1 : 0] rx_mvb_usermeta;
    logic [MFB_REGIONS*$clog2(PKT_MTU+1)-1 : 0] rx_mvb_frame_length;
    logic [MFB_REGIONS*$clog2(PKT_MTU+1)-1 : 0] rx_mvb_ext_size;
    logic [MFB_REGIONS                  -1 : 0] rx_mvb_ext_only;
    logic [MFB_REGIONS                  -1 : 0] rx_mvb_ext_en;

    MFB_FRAME_EXTENDER  #(
        .MFB_REGIONS     (MFB_REGIONS),
        .MFB_REGION_SIZE (MFB_REGION_SIZE),
        .MFB_BLOCK_SIZE  (MFB_BLOCK_SIZE),
        .MFB_ITEM_WIDTH  (MFB_ITEM_WIDTH),
        .PKT_MTU         (PKT_MTU),
        .MVB_FIFO_DEPTH  (MVB_FIFO_DEPTH),
        .MFB_FIFO_DEPTH  (MFB_FIFO_DEPTH),
        .USERMETA_WIDTH  (USERMETA_WIDTH),
        .DEVICE          (DEVICE)
    ) VHDL_DUT_U (
        .CLK   (CLK),
        .RESET (RST),

        .RX_MVB_USERMETA     (rx_mvb_usermeta),
        .RX_MVB_FRAME_LENGTH (rx_mvb_frame_length),
        .RX_MVB_EXT_SIZE     (rx_mvb_ext_size),
        .RX_MVB_EXT_ONLY     (rx_mvb_ext_only),
        .RX_MVB_EXT_EN       (rx_mvb_ext_en),
        .RX_MVB_VLD          (mvb_rx.VLD),
        .RX_MVB_SRC_RDY      (mvb_rx.SRC_RDY),
        .RX_MVB_DST_RDY      (mvb_rx.DST_RDY),

        .RX_MFB_DATA    (mfb_rx.DATA),
        .RX_MFB_SOF     (mfb_rx.SOF),
        .RX_MFB_EOF     (mfb_rx.EOF),
        .RX_MFB_SOF_POS (mfb_rx.SOF_POS),
        .RX_MFB_EOF_POS (mfb_rx.EOF_POS),
        .RX_MFB_SRC_RDY (mfb_rx.SRC_RDY),
        .RX_MFB_DST_RDY (mfb_rx.DST_RDY),

        .TX_MVB_USERMETA (mvb_tx.DATA),
        .TX_MVB_VLD      (mvb_tx.VLD),
        .TX_MVB_SRC_RDY  (mvb_tx.SRC_RDY),
        .TX_MVB_DST_RDY  (mvb_tx.DST_RDY),

        .TX_MFB_DATA     (mfb_tx.DATA),
        .TX_MFB_USERMETA (mfb_tx.META),
        .TX_MFB_SOF      (mfb_tx.SOF),
        .TX_MFB_EOF      (mfb_tx.EOF),
        .TX_MFB_SOF_POS  (mfb_tx.SOF_POS),
        .TX_MFB_EOF_POS  (mfb_tx.EOF_POS),
        .TX_MFB_SRC_RDY  (mfb_tx.SRC_RDY),
        .TX_MFB_DST_RDY  (mfb_tx.DST_RDY)
    );

    generate;
        for (genvar i = 0; i < MFB_REGIONS; i++) begin : gen_i
            logic [RX_MVB_ITEM_WIDTH-1 : 0] rx_mvb_slice;
            assign rx_mvb_slice = mvb_rx.DATA[RX_MVB_ITEM_WIDTH*(i+1)-1 -: RX_MVB_ITEM_WIDTH];

            assign rx_mvb_ext_en      [i]                                              = rx_mvb_slice[1                                      -1 -: 1];
            assign rx_mvb_ext_only    [i]                                              = rx_mvb_slice[1+1                                    -1 -: 1];
            assign rx_mvb_ext_size    [$clog2(PKT_MTU+1)*(i+1)-1 -: $clog2(PKT_MTU+1)] = rx_mvb_slice[$clog2(PKT_MTU+1)+1+1                  -1 -: $clog2(PKT_MTU+1)];
            assign rx_mvb_frame_length[$clog2(PKT_MTU+1)*(i+1)-1 -: $clog2(PKT_MTU+1)] = rx_mvb_slice[$clog2(PKT_MTU+1)+$clog2(PKT_MTU+1)+1+1-1 -: $clog2(PKT_MTU+1)];
            assign rx_mvb_usermeta    [USERMETA_WIDTH   *(i+1)-1 -: USERMETA_WIDTH   ] = rx_mvb_slice[RX_MVB_ITEM_WIDTH                      -1 -: USERMETA_WIDTH];
        end
    endgenerate

endmodule
