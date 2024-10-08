// dut.sv
// Copyright (C) 2020 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;

module DUT (
    input logic CLK,
    input logic RESET,
    iMfbTx.dut TX,
    iMi32.dut  MI32
);

    MFB_GENERATOR_MI32 #(
        .REGIONS        (MFB_REGIONS),
        .REGION_SIZE    (MFB_REGION_SIZE),
        .BLOCK_SIZE     (MFB_BLOCK_SIZE),
        .ITEM_WIDTH     (MFB_ITEM_WIDTH),
        .LENGTH_WIDTH   (LENGTH_WIDTH),
        .CHANNELS_WIDTH (CHANNELS_WIDTH),
        .PKT_CNT_WIDTH  (PKT_CNT_WIDTH),
        .USE_PACP_ARCH  (USE_PACP_ARCH),
        .DEVICE         (DEVICE)
    ) VHDL_DUT_U (
        .CLK             (CLK),
        .RST             (RESET),
        // -----------------------
        .MI_DWR          (MI32.DWR),
        .MI_ADDR         (MI32.ADDR),
        .MI_RD           (MI32.RD),
        .MI_WR           (MI32.WR),
        .MI_BE           (MI32.BE),
        .MI_DRD          (MI32.DRD),
        .MI_ARDY         (MI32.ARDY),
        .MI_DRDY         (MI32.DRDY),
        // -----------------------
        .TX_MFB_DATA     (TX.DATA),
        .TX_MFB_META     (),
        .TX_MFB_SOF_POS  (TX.SOF_POS),
        .TX_MFB_EOF_POS  (TX.EOF_POS),
        .TX_MFB_SOF      (TX.SOF),
        .TX_MFB_EOF      (TX.EOF),
        .TX_MFB_SRC_RDY  (TX.SRC_RDY),
        .TX_MFB_DST_RDY  (TX.DST_RDY)
    );

endmodule
