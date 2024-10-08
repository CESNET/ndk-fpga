// dut.sv: Design under test
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s):  Vladislav Valek <xvalek14@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause


import test::*;

module DUT (
    input logic     CLK,
    input logic     RST,
    mfb_if.dut_rx   mfb_rx,
    mfb_if.dut_tx   mfb_tx
    );

    MFB_TO_LBUS_RECONF VHDL_DUT_U (
        .CLK                (CLK),
        .RST                (RST),

        .RX_MFB_DATA        (mfb_rx.DATA),
        .RX_MFB_SOF_POS     (mfb_rx.SOF_POS),
        .RX_MFB_EOF_POS     (mfb_rx.EOF_POS),
        .RX_MFB_SOF         (mfb_rx.SOF),
        .RX_MFB_EOF         (mfb_rx.EOF),
        .RX_MFB_SRC_RDY     (mfb_rx.SRC_RDY),
        .RX_MFB_DST_RDY     (mfb_rx.DST_RDY),

        .TX_MFB_DATA        (mfb_tx.DATA),
        .TX_MFB_SOF_POS     (mfb_tx.SOF_POS),
        .TX_MFB_EOF_POS     (mfb_tx.EOF_POS),
        .TX_MFB_SOF         (mfb_tx.SOF),
        .TX_MFB_EOF         (mfb_tx.EOF),
        .TX_MFB_SRC_RDY     (mfb_tx.SRC_RDY),
        .TX_MFB_DST_RDY     (mfb_tx.DST_RDY)
    );


endmodule
