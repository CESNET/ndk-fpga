// dut.sv
// Copyright (C) 2019 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;

module DUT (
    input logic RX_CLK,
    input logic RX_CLK_X2,
    input logic RX_RESET,
    input logic TX_CLK,
    input logic TX_RESET,
    input logic MI_CLK,
    input logic MI_RESET,
    iMfbRx.dut RX,
    iMfbTx.dut TX,
    iMi32.dut  MI32
);

    TX_MAC_LITE #(
        .TX_REGIONS      (TX_REGIONS),
        .TX_REGION_SIZE  (TX_REGION_SIZE),
        .TX_BLOCK_SIZE   (TX_BLOCK_SIZE),
        .TX_ITEM_WIDTH   (TX_ITEM_WIDTH),
        .RX_REGIONS      (RX_REGIONS),
        .RX_REGION_SIZE  (RX_REGION_SIZE),
        .RX_BLOCK_SIZE   (RX_BLOCK_SIZE),
        .RX_ITEM_WIDTH   (RX_ITEM_WIDTH),
        .RX_INCLUDE_CRC  (RX_INCLUDE_CRC),
        .RX_INCLUDE_IPG  (RX_INCLUDE_IPG),
        .CRC_INSERT_EN   (CRC_INSERT_EN),
        .IPG_GENERATE_EN (IPG_GENERATE_EN)
    ) VHDL_DUT_U (
        .MI_CLK          (MI_CLK),
        .MI_RESET        (MI_RESET),
        .MI_DWR          (MI32.DWR),
        .MI_ADDR         (MI32.ADDR),
        .MI_RD           (MI32.RD),
        .MI_WR           (MI32.WR),
        .MI_BE           (MI32.BE),
        .MI_DRD          (MI32.DRD),
        .MI_ARDY         (MI32.ARDY),
        .MI_DRDY         (MI32.DRDY),
        // -----------------------
        .RX_CLK          (RX_CLK),
        .RX_CLK_X2       (RX_CLK_X2),
        .RX_RESET        (RX_RESET),
        .RX_MFB_DATA     (RX.DATA),
        .RX_MFB_SOF_POS  (RX.SOF_POS),
        .RX_MFB_EOF_POS  (RX.EOF_POS),
        .RX_MFB_SOF      (RX.SOF),
        .RX_MFB_EOF      (RX.EOF),
        .RX_MFB_SRC_RDY  (RX.SRC_RDY),
        .RX_MFB_DST_RDY  (RX.DST_RDY),
        // -----------------------
        .TX_CLK          (TX_CLK),
        .TX_RESET        (TX_RESET),
        .TX_MFB_DATA     (TX.DATA),
        .TX_MFB_SOF_POS  (TX.SOF_POS),
        .TX_MFB_EOF_POS  (TX.EOF_POS),
        .TX_MFB_SOF      (TX.SOF),
        .TX_MFB_EOF      (TX.EOF),
        .TX_MFB_SRC_RDY  (TX.SRC_RDY),
        .TX_MFB_DST_RDY  (TX.DST_RDY)
    );

endmodule
