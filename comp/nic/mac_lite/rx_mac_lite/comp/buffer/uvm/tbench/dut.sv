// dut.sv: Design under test
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


module DUT #(
        REGIONS     ,
        REGION_SIZE ,
        BLOCK_SIZE  ,
        ITEM_WIDTH  ,
        META_WIDTH  ,
        DEVICE
    )(
        input logic     RX_CLK,
        input logic     RX_RST,
        input logic     TX_CLK,
        input logic     TX_RST,
        mfb_if.dut_rx   mfb_rx,
        mvb_if.dut_tx   mvb_tx,
        mfb_if.dut_tx   mfb_tx
    );

    logic [REGIONS-1 : 0] rx_error = '{REGIONS{1'b0}};
    RX_MAC_LITE_BUFFER #(
        .REGIONS          (REGIONS)               ,
        .REGION_SIZE      (REGION_SIZE)           ,
        .BLOCK_SIZE       (BLOCK_SIZE)            ,
        .ITEM_WIDTH       (ITEM_WIDTH)            ,
        .META_WIDTH       (META_WIDTH)            ,
        .DEVICE           (DEVICE)
    ) VHDL_DUT_U (
        .RX_CLK             (RX_CLK)                  ,
        .RX_RESET           (RX_RST)                  ,

        .RX_DATA            (mfb_rx.DATA)             ,
        .RX_METADATA        (mfb_rx.META)             ,
        .RX_ERROR           (rx_error),
        .RX_SOF_POS         (mfb_rx.SOF_POS)          ,
        .RX_EOF_POS         (mfb_rx.EOF_POS)          ,
        .RX_SOF             (mfb_rx.SOF)              ,
        .RX_EOF             (mfb_rx.EOF)              ,
        .RX_SRC_RDY         (mfb_rx.SRC_RDY)          ,

        .TX_CLK             (TX_CLK)                  ,
        .TX_RESET           (TX_RST)                  ,

        .TX_MVB_DATA        (mvb_tx.DATA)             ,
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

    assign mfb_rx.DST_RDY = 1'b1;

endmodule
