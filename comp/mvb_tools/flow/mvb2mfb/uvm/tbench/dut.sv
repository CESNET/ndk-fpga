// dut.sv: Design under test
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

module DUT #(
    int unsigned MVB_ITEMS,
    int unsigned MVB_ITEM_WIDTH_RAW,
    int unsigned MFB_REGIONS,
    int unsigned MFB_REGION_SIZE,
    int unsigned MFB_BLOCK_SIZE,
    int unsigned MFB_ITEM_WIDTH,
    int unsigned MFB_ALIGNMENT,
    int unsigned MFB_META_WIDTH,
    int unsigned MVB_ITEM_WIDTH,
    string DEVICE
) (
    input logic     CLK,
    input logic     RST,
    mvb_if.dut_rx   mvb_rx,
    mfb_if.dut_tx   mfb_tx
    );

    logic [MVB_ITEMS*MFB_META_WIDTH-1 : 0]     mvb_meta;
    logic [MVB_ITEMS*MVB_ITEM_WIDTH_RAW-1 : 0] mvb_data;

    generate
        for (genvar i = 0; i < MVB_ITEMS; i++) begin
            assign mvb_data[(i+1)*MVB_ITEM_WIDTH_RAW-1 : MVB_ITEM_WIDTH_RAW*i] = mvb_rx.DATA[i*MVB_ITEM_WIDTH +: MVB_ITEM_WIDTH_RAW];
            assign mvb_meta[(i+1)*MFB_META_WIDTH-1 : MFB_META_WIDTH*i]         = mvb_rx.DATA[i*MVB_ITEM_WIDTH+MVB_ITEM_WIDTH_RAW +: MFB_META_WIDTH];
        end
    endgenerate

    MVB2MFB #(
        .MVB_ITEMS        (MVB_ITEMS)                 ,
        .MVB_ITEM_WIDTH   (MVB_ITEM_WIDTH_RAW)        ,

        .MFB_REGIONS      (MFB_REGIONS)               ,
        .MFB_REGION_SIZE  (MFB_REGION_SIZE)           ,
        .MFB_BLOCK_SIZE   (MFB_BLOCK_SIZE)            ,
        .MFB_ITEM_WIDTH   (MFB_ITEM_WIDTH)            ,

        .MFB_ALIGNMENT    (MFB_ALIGNMENT)             ,
        .META_WIDTH       (MFB_META_WIDTH)            ,
        .DEVICE           (DEVICE)
    ) VHDL_DUT_U (
        .CLK                (CLK)                     ,
        .RESET              (RST)                     ,

        .RX_MVB_DATA        (mvb_data)                ,
        .RX_MVB_META        (mvb_meta)                ,
        .RX_MVB_VLD         (mvb_rx.VLD)              ,
        .RX_MVB_SRC_RDY     (mvb_rx.SRC_RDY)          ,
        .RX_MVB_DST_RDY     (mvb_rx.DST_RDY)          ,

        .TX_MFB_DATA        (mfb_tx.DATA)             ,
        .TX_MFB_META        (mfb_tx.META)             ,
        .TX_MFB_SOF_POS     (mfb_tx.SOF_POS)          ,
        .TX_MFB_EOF_POS     (mfb_tx.EOF_POS)          ,
        .TX_MFB_SOF         (mfb_tx.SOF)              ,
        .TX_MFB_EOF         (mfb_tx.EOF)              ,
        .TX_MFB_SRC_RDY     (mfb_tx.SRC_RDY)          ,
        .TX_MFB_DST_RDY     (mfb_tx.DST_RDY)

    );


endmodule
