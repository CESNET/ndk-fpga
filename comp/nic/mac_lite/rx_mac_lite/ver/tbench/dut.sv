// dut.sv
// Copyright (C) 2019 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;

module DUT (
    input logic RX_CLK,
    input logic RX_RESET,
    input logic TX_CLK,
    input logic TX_RESET,
    input logic MI_CLK,
    input logic MI_RESET,
    iMi32.dut  MI,
    iMfbRx.dut RX_MFB,
    iMfbTx.dut TX_MFB,
    iMvbTx.dut TX_MVB
);

    assign RX_MFB.DST_RDY = 1'b1;

    RX_MAC_LITE #(
        .RX_REGIONS      (RX_REGIONS),
        .RX_REGION_SIZE  (RX_REGION_SIZE),
        .RX_BLOCK_SIZE   (RX_BLOCK_SIZE),
        .RX_ITEM_WIDTH   (RX_ITEM_WIDTH),
        .TX_REGIONS      (TX_REGIONS),
        .TX_REGION_SIZE  (TX_REGION_SIZE),
        .TX_BLOCK_SIZE   (TX_BLOCK_SIZE),
        .TX_ITEM_WIDTH   (TX_ITEM_WIDTH),
        .RESIZE_BUFFER   (RESIZE_BUFFER),
        .CRC_IS_RECEIVED (CRC_IS_RECEIVED),
        .CRC_CHECK_EN    (CRC_CHECK_EN),
        .CRC_REMOVE_EN   (CRC_REMOVE_EN),
        .MAC_CHECK_EN    (MAC_CHECK_EN),
        .TIMESTAMP_EN    (TIMESTAMP_EN),
        .MAC_COUNT       (MAC_COUNT_MAX)
    ) VHDL_DUT_U (
        .RX_CLK          (RX_CLK),
        .RX_RESET        (RX_RESET),

        .RX_MFB_DATA     (RX_MFB.DATA),
        .RX_MFB_SOF_POS  (RX_MFB.SOF_POS),
        .RX_MFB_EOF_POS  (RX_MFB.EOF_POS),
        .RX_MFB_SOF      (RX_MFB.SOF),
        .RX_MFB_EOF      (RX_MFB.EOF),
        .RX_MFB_ERROR    (RX_MFB.META),
        .RX_MFB_SRC_RDY  (RX_MFB.SRC_RDY),

        .ADAPTER_LINK_UP (1'b1),

        .LINK_UP         (),
        .INCOMING_FRAME  (),

        .TSU_TS_NS       (),
        .TSU_TS_DV       (),

        .TX_CLK          (TX_CLK),
        .TX_RESET        (TX_RESET),

        .TX_MFB_DATA     (TX_MFB.DATA),
        .TX_MFB_SOF_POS  (TX_MFB.SOF_POS),
        .TX_MFB_EOF_POS  (TX_MFB.EOF_POS),
        .TX_MFB_SOF      (TX_MFB.SOF),
        .TX_MFB_EOF      (TX_MFB.EOF),
        .TX_MFB_SRC_RDY  (TX_MFB.SRC_RDY),
        .TX_MFB_DST_RDY  (TX_MFB.DST_RDY),

        .TX_MVB_DATA     (TX_MVB.DATA),
        .TX_MVB_VLD      (TX_MVB.VLD),
        .TX_MVB_SRC_RDY  (TX_MVB.SRC_RDY),
        .TX_MVB_DST_RDY  (TX_MVB.DST_RDY),

        .MI_CLK          (MI_CLK),
        .MI_RESET        (MI_RESET),
        .MI_DWR          (MI.DWR),
        .MI_ADDR         (MI.ADDR),
        .MI_RD           (MI.RD),
        .MI_WR           (MI.WR),
        .MI_BE           (MI.BE),
        .MI_DRD          (MI.DRD),
        .MI_ARDY         (MI.ARDY),
        .MI_DRDY         (MI.DRDY)
    );

endmodule
