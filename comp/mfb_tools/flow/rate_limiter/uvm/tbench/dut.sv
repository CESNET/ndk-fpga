// dut.sv: Design under test
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Tomas Hak <xhakto01@vut.cz>

// SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT (
    input logic           CLK,
    input logic           RST,
    mfb_if.dut_rx         mfb_rx,
    mfb_if.dut_tx         mfb_tx,
    mi_if.dut_slave       mi
    );

    RATE_LIMITER #(
        .MI_DATA_WIDTH   (MI_DATA_WIDTH),
        .MI_ADDR_WIDTH   (MI_ADDR_WIDTH),
        .MFB_REGIONS     (MFB_REGIONS),
        .MFB_REGION_SIZE (MFB_REGION_SIZE),
        .MFB_BLOCK_SIZE  (MFB_BLOCK_SIZE),
        .MFB_ITEM_WIDTH  (MFB_ITEM_WIDTH),
        .MFB_META_WIDTH  (MFB_META_WIDTH),
        .SECTION_LENGTH  (SECTION_LENGTH),
        .INTERVAL_LENGTH (INTERVAL_LENGTH),
        .INTERVAL_COUNT  (INTERVAL_COUNT),
        .OUTPUT_SPEED    (OUTPUT_SPEED),
        .FREQUENCY       (FREQUENCY),
        .DEVICE          (DEVICE)
    ) VHDL_DUT_U (
        .CLK             (CLK),
        .RESET           (RST),

        .MI_DWR          (mi.DWR),
        .MI_ADDR         (mi.ADDR),
        .MI_RD           (mi.RD),
        .MI_WR           (mi.WR),
        .MI_BE           (mi.BE),
        .MI_DRD          (mi.DRD),
        .MI_ARDY         (mi.ARDY),
        .MI_DRDY         (mi.DRDY),

        .RX_MFB_DATA     (mfb_rx.DATA),
        .RX_MFB_META     (mfb_rx.META),
        .RX_MFB_SOF      (mfb_rx.SOF),
        .RX_MFB_EOF      (mfb_rx.EOF),
        .RX_MFB_SOF_POS  (mfb_rx.SOF_POS),
        .RX_MFB_EOF_POS  (mfb_rx.EOF_POS),
        .RX_MFB_SRC_RDY  (mfb_rx.SRC_RDY),
        .RX_MFB_DST_RDY  (mfb_rx.DST_RDY),

        .TX_MFB_DATA     (mfb_tx.DATA),
        .TX_MFB_META     (mfb_tx.META),
        .TX_MFB_SOF      (mfb_tx.SOF),
        .TX_MFB_EOF      (mfb_tx.EOF),
        .TX_MFB_SOF_POS  (mfb_tx.SOF_POS),
        .TX_MFB_EOF_POS  (mfb_tx.EOF_POS),
        .TX_MFB_SRC_RDY  (mfb_tx.SRC_RDY),
        .TX_MFB_DST_RDY  (mfb_tx.DST_RDY)
    );
endmodule
