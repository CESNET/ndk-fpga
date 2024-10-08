// dut.sv
// Copyright (C) 2020 CESNET z. s. p. o.
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
    iMiiTx.dut TX,
    iMi32.dut  MI32
);

    TX_MAC_LITE_UMII #(
        .MII_DW          (MII_DATA_WIDTH),
        .RX_REGIONS      (RX_REGIONS),
        .RX_BLOCK_SIZE   (RX_BLOCK_SIZE),
        .RX_ITEM_WIDTH   (RX_ITEM_WIDTH),
        .RX_REGION_SIZE  (RX_REGION_SIZE),
        .RX_INCLUDE_CRC  (RX_INCLUDE_CRC),
        .RX_INCLUDE_IPG  (RX_INCLUDE_IPG)
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
        .MII_CLK         (TX_CLK),
        .MII_RESET       (TX_RESET),
        .MII_TXD         (TX.TXD),
        .MII_TXC         (TX.TXC),
        .MII_VLD         (),
        .MII_RDY         (),
        // -----------------------
        .OUTGOING_FRAME  ()
    );

endmodule
