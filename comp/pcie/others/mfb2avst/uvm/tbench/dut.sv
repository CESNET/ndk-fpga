//-- dut.sv: Design under test
//-- Copyright (C) 2023 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT (
    input logic     CLK,
    input logic     RST,
    mfb_if.dut_rx   mfb_rx,
    avst_if.dut_tx  mfb_avst
    );

    PCIE_MFB2AVST #(
        .REGIONS     (MFB_REGIONS),
        .REGION_SIZE (MFB_REGION_SIZE),
        .BLOCK_SIZE  (MFB_BLOCK_SIZE),
        .ITEM_WIDTH  (MFB_ITEM_WIDTH),
        .META_WIDTH  (META_WIDTH)
    ) VHDL_DUT_U (
        .CLK            (CLK),
        .RST            (RST),

        .RX_MFB_DATA    (mfb_rx.DATA),
        .RX_MFB_META    (mfb_rx.META),
        .RX_MFB_SOF     (mfb_rx.SOF),
        .RX_MFB_EOF     (mfb_rx.EOF),
        .RX_MFB_EOF_POS (mfb_rx.EOF_POS),
        .RX_MFB_SRC_RDY (mfb_rx.SRC_RDY),
        .RX_MFB_DST_RDY (mfb_rx.DST_RDY),

        .TX_AVST_DATA      (mfb_avst.DATA),
        .TX_AVST_META      (mfb_avst.META),
        .TX_AVST_SOP       (mfb_avst.SOP),
        .TX_AVST_EOP       (mfb_avst.EOP),
        .TX_AVST_EMPTY     (mfb_avst.EMPTY),
        .TX_AVST_VALID     (mfb_avst.VALID),
        .TX_AVST_READY     (mfb_avst.READY)

    );


endmodule
