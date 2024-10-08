// dut.sv: Design under test
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kříž <xkrizd01@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


import test::*;

module DUT (
    input logic   CLK,
    input logic   RST,
    mfb_if.dut_rx mfb_rx,
    mfb_if.dut_tx mfb_tx,
    mvb_if.dut_rx mvb_rx,
    mvb_if.dut_tx mvb_tx
    );

    FRAME_UNPACKER #(
        .MFB_REGIONS      (MFB_REGIONS)               ,
        .MFB_REGION_SIZE  (MFB_REGION_SIZE)           ,
        .MFB_BLOCK_SIZE   (MFB_BLOCK_SIZE)            ,
        .MFB_ITEM_WIDTH   (MFB_ITEM_WIDTH)            ,

        .HEADER_LENGTH    (HEADER_SIZE/MFB_ITEM_WIDTH),
        .MVB_ITEM_WIDTH   (MVB_ITEM_WIDTH),
        .UNPACKING_STAGES (UNPACKING_STAGES)          ,
        .META_OUT_MODE    (META_OUT_MODE)             ,
        .PKT_MTU          (PKT_MTU)                   ,
        .DEVICE           (DEVICE)
    ) VHDL_DUT_U (
        .CLK                (CLK)                     ,
        .RESET              (RST)                     ,

        .RX_MVB_DATA        (mvb_rx.DATA)             ,
        .RX_MVB_VLD         (mvb_rx.VLD)              ,
        .RX_MVB_SRC_RDY     (mvb_rx.SRC_RDY)          ,
        .RX_MVB_DST_RDY     (mvb_rx.DST_RDY)          ,

        .RX_MFB_DATA        (mfb_rx.DATA)             ,
        .RX_MFB_SOF_POS     (mfb_rx.SOF_POS)          ,
        .RX_MFB_EOF_POS     (mfb_rx.EOF_POS)          ,
        .RX_MFB_SOF         (mfb_rx.SOF)              ,
        .RX_MFB_EOF         (mfb_rx.EOF)              ,
        .RX_MFB_SRC_RDY     (mfb_rx.SRC_RDY)          ,
        .RX_MFB_DST_RDY     (mfb_rx.DST_RDY)          ,

        .TX_MFB_DATA        (mfb_tx.DATA)             ,
        .TX_MFB_META        (mfb_tx.META)             ,
        .TX_MFB_SOF_POS     (mfb_tx.SOF_POS)          ,
        .TX_MFB_EOF_POS     (mfb_tx.EOF_POS)          ,
        .TX_MFB_SOF         (mfb_tx.SOF)              ,
        .TX_MFB_EOF         (mfb_tx.EOF)              ,
        .TX_MFB_SRC_RDY     (mfb_tx.SRC_RDY)          ,
        .TX_MFB_DST_RDY     (mfb_tx.DST_RDY)          ,

        .TX_MVB_DATA        (mvb_tx.DATA)             ,
        .TX_MVB_VLD         (mvb_tx.VLD)              ,
        .TX_MVB_SRC_RDY     (mvb_tx.SRC_RDY)          ,
        .TX_MVB_DST_RDY     (mvb_tx.DST_RDY)
    );


endmodule
