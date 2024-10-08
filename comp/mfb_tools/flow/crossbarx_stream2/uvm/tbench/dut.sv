// dut.sv: Design under test
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


import test::*;

module DUT (
    input logic     CLK,
    input logic     CLK_X2,
    input logic     RST,
    mvb_if.dut_rx   mvb_rx,
    mfb_if.dut_rx   mfb_rx,
    mvb_if.dut_tx   mvb_tx,
    mfb_if.dut_tx   mfb_tx
);
    logic [RX_MFB_REGIONS*USERMETA_W-1 : 0] mvb_rx_usermeta;//     [IN_STREAMS-1:0];
    logic [RX_MFB_REGIONS-1 : 0]            mvb_rx_discard;//      [IN_STREAMS-1:0];
    logic [RX_MFB_REGIONS*MOD_W-1 : 0]      mvb_rx_mod_sof_size;// [IN_STREAMS-1:0];
    logic [RX_MFB_REGIONS-1 : 0]            mvb_rx_mod_sof_en;//   [IN_STREAMS-1:0];
    logic [RX_MFB_REGIONS-1 : 0]            mvb_rx_mod_sof_type;// [IN_STREAMS-1:0];
    logic [RX_MFB_REGIONS*MOD_W-1 : 0]      mvb_rx_mod_eof_size;// [IN_STREAMS-1:0];
    logic [RX_MFB_REGIONS-1 : 0]            mvb_rx_mod_eof_en;//   [IN_STREAMS-1:0];
    logic [RX_MFB_REGIONS-1 : 0]            mvb_rx_mod_eof_type;// [IN_STREAMS-1:0];

    for (genvar rr = 0; rr < RX_MFB_REGIONS; rr++) begin
        assign mvb_rx_usermeta     [(rr+1)*USERMETA_W -1 -: USERMETA_W] = mvb_rx.DATA[(rr*RX_MVB_ITEM_W)+USERMETA_W-1 -: USERMETA_W];
        assign mvb_rx_discard      [rr]                                 = mvb_rx.DATA[(rr*RX_MVB_ITEM_W)+USERMETA_W];
        assign mvb_rx_mod_sof_size [(rr+1)*MOD_W      -1 -: MOD_W]      = mvb_rx.DATA[(rr*RX_MVB_ITEM_W)+USERMETA_W+MOD_W+1-1 -: MOD_W];
        assign mvb_rx_mod_sof_en   [rr]                                 = mvb_rx.DATA[(rr*RX_MVB_ITEM_W)+USERMETA_W+MOD_W+1];
        assign mvb_rx_mod_sof_type [rr]                                 = mvb_rx.DATA[(rr*RX_MVB_ITEM_W)+USERMETA_W+MOD_W+2];
        assign mvb_rx_mod_eof_size [(rr+1)*MOD_W      -1 -: MOD_W]      = mvb_rx.DATA[(rr*RX_MVB_ITEM_W)+USERMETA_W+MOD_W+3+MOD_W-1 -: MOD_W];
        assign mvb_rx_mod_eof_en   [rr]                                 = mvb_rx.DATA[(rr*RX_MVB_ITEM_W)+USERMETA_W+MOD_W+3+MOD_W];
        assign mvb_rx_mod_eof_type [rr]                                 = mvb_rx.DATA[(rr*RX_MVB_ITEM_W)+USERMETA_W+MOD_W+3+MOD_W+1];
    end

    MFB_CROSSBARX_STREAM2 #(
        .MFB_REGIONS      (RX_MFB_REGIONS)            ,
        .MFB_REGION_SIZE  (RX_MFB_REGION_S)           ,
        .MFB_BLOCK_SIZE   (RX_MFB_BLOCK_S)            ,
        .MFB_ITEM_WIDTH   (RX_MFB_ITEM_W)             ,
        .USERMETA_WIDTH   (USERMETA_W)                ,
        .MOD_WIDTH        (MOD_W)                     ,
        .DEVICE           (DEVICE)
    ) VHDL_DUT_U (
        .CLK                (CLK)                     ,
        .CLK_X2             (CLK_X2)                  ,
        .RESET              (RST)                     ,

        .RX_MVB_USERMETA     (mvb_rx_usermeta)        ,
        .RX_MVB_DISCARD      (mvb_rx_discard)         ,
        .RX_MVB_MOD_SOF_SIZE (mvb_rx_mod_sof_size)    ,
        .RX_MVB_MOD_SOF_TYPE (mvb_rx_mod_sof_type)    ,
        .RX_MVB_MOD_SOF_EN   (mvb_rx_mod_sof_en)      ,
        .RX_MVB_MOD_EOF_SIZE (mvb_rx_mod_eof_size)    ,
        .RX_MVB_MOD_EOF_TYPE (mvb_rx_mod_eof_type)    ,
        .RX_MVB_MOD_EOF_EN   (mvb_rx_mod_eof_en)      ,
        .RX_MVB_VLD          (mvb_rx.VLD)             ,
        .RX_MVB_SRC_RDY      (mvb_rx.SRC_RDY)         ,
        .RX_MVB_DST_RDY      (mvb_rx.DST_RDY)         ,

        .RX_MFB_DATA        (mfb_rx.DATA)             ,
        .RX_MFB_SOF_POS     (mfb_rx.SOF_POS)          ,
        .RX_MFB_EOF_POS     (mfb_rx.EOF_POS)          ,
        .RX_MFB_SOF         (mfb_rx.SOF)              ,
        .RX_MFB_EOF         (mfb_rx.EOF)              ,
        .RX_MFB_SRC_RDY     (mfb_rx.SRC_RDY)          ,
        .RX_MFB_DST_RDY     (mfb_rx.DST_RDY)          ,

        .TX_MVB_USERMETA    (mvb_tx.DATA)             ,
        .TX_MVB_VLD         (mvb_tx.VLD)              ,
        .TX_MVB_SRC_RDY     (mvb_tx.SRC_RDY)          ,
        .TX_MVB_DST_RDY     (mvb_tx.DST_RDY)          ,

        .TX_MFB_DATA        (mfb_tx.DATA)             ,
        .TX_MFB_SOF_POS     (mfb_tx.SOF_POS)          ,
        .TX_MFB_EOF_POS     (mfb_tx.EOF_POS)          ,
        .TX_MFB_SOF         (mfb_tx.SOF)              ,
        .TX_MFB_EOF         (mfb_tx.EOF)              ,
        .TX_MFB_SRC_RDY     (mfb_tx.SRC_RDY)          ,
        .TX_MFB_DST_RDY     (mfb_tx.DST_RDY)

    );

endmodule
