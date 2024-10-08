// dut.sv: Design under test
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kříž <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


import test::*;

module DUT (
    input logic     CLK,
    input logic     RST,
    mfb_if.dut_rx   mfb_rx,
    mvb_if.dut_rx   mvb_rx,
    mfb_if.dut_tx   mfb_tx
    );

    logic [MFB_REGIONS*MFB_META_WIDTH-1 : 0] meta;
    logic [MFB_REGIONS*MVB_ITEM_WIDTH-1 : 0] meta_new;

    generate
        for (genvar i = 0; i < MFB_REGIONS; i++) begin
            assign mfb_tx.META[i*(MVB_ITEM_WIDTH + MFB_META_WIDTH)+MVB_ITEM_WIDTH+MFB_META_WIDTH-1 -: MFB_META_WIDTH] = meta[(i+1)*MFB_META_WIDTH-1 : MFB_META_WIDTH*i];

            assign mfb_tx.META[i*(MFB_META_WIDTH + MVB_ITEM_WIDTH)+MVB_ITEM_WIDTH-1 -: MVB_ITEM_WIDTH] = meta_new[(i+1)*MVB_ITEM_WIDTH-1 -: MVB_ITEM_WIDTH];
        end
    endgenerate

    METADATA_INSERTOR #(
        .MVB_ITEMS        (MVB_ITEMS)                 ,
        .MVB_ITEM_WIDTH   (MVB_ITEM_WIDTH)            ,

        .MFB_REGIONS      (MFB_REGIONS)               ,
        .MFB_REGION_SIZE  (MFB_REGION_SIZE)           ,
        .MFB_BLOCK_SIZE   (MFB_BLOCK_SIZE)            ,
        .MFB_ITEM_WIDTH   (MFB_ITEM_WIDTH)            ,
        .MFB_META_WIDTH   (MFB_META_WIDTH)            ,

        .INSERT_MODE      (INSERT_MODE)               ,
        .MVB_FIFO_SIZE    (MVB_FIFO_SIZE)             ,
        .DEVICE           (DEVICE)
    ) VHDL_DUT_U (
        .CLK                (CLK)                     ,
        .RESET              (RST)                     ,

        .RX_MVB_DATA        (mvb_rx.DATA)             ,
        .RX_MVB_VLD         (mvb_rx.VLD)              ,
        .RX_MVB_SRC_RDY     (mvb_rx.SRC_RDY)          ,
        .RX_MVB_DST_RDY     (mvb_rx.DST_RDY)          ,

        .RX_MFB_DATA        (mfb_rx.DATA)             ,
        .RX_MFB_META        (mfb_rx.META)             ,
        .RX_MFB_SOF_POS     (mfb_rx.SOF_POS)          ,
        .RX_MFB_EOF_POS     (mfb_rx.EOF_POS)          ,
        .RX_MFB_SOF         (mfb_rx.SOF)              ,
        .RX_MFB_EOF         (mfb_rx.EOF)              ,
        .RX_MFB_SRC_RDY     (mfb_rx.SRC_RDY)          ,
        .RX_MFB_DST_RDY     (mfb_rx.DST_RDY)          ,

        .TX_MFB_DATA        (mfb_tx.DATA)             ,
        .TX_MFB_META        (meta)                    ,
        .TX_MFB_META_NEW    (meta_new)                ,
        .TX_MFB_SOF_POS     (mfb_tx.SOF_POS)          ,
        .TX_MFB_EOF_POS     (mfb_tx.EOF_POS)          ,
        .TX_MFB_SOF         (mfb_tx.SOF)              ,
        .TX_MFB_EOF         (mfb_tx.EOF)              ,
        .TX_MFB_SRC_RDY     (mfb_tx.SRC_RDY)          ,
        .TX_MFB_DST_RDY     (mfb_tx.DST_RDY)

    );


endmodule
