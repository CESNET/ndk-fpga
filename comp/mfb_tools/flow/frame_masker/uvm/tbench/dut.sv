// dut.sv: Design under test
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kondys <kondys@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


import test::*;

module DUT (
    input logic   CLK,
    input logic   RST,
    mfb_if.dut_rx mfb_rx,
    mvb_if.dut_rx mvb_rx,
    mfb_if.dut_tx mfb_tx
);

    assign mvb_rx.VLD     = 1; // TODO
    assign mvb_rx.SRC_RDY = 1; // TODO
    assign mvb_rx.DST_RDY = mfb_tx.DST_RDY;

    MFB_FRAME_MASKER #(
        .REGIONS     (MFB_REGIONS    ),
        .REGION_SIZE (MFB_REGION_SIZE),
        .BLOCK_SIZE  (MFB_BLOCK_SIZE ),
        .ITEM_WIDTH  (MFB_ITEM_WIDTH ),
        .META_WIDTH  (MFB_META_WIDTH ),
        .USE_PIPE    (USE_PIPE       )
    ) VHDL_DUT_U (
        .CLK             (CLK),
        .RESET           (RST),

        .RX_DATA         (mfb_rx.DATA   ),
        .RX_META         (mfb_rx.META   ),
        .RX_SOF_POS      (mfb_rx.SOF_POS),
        .RX_EOF_POS      (mfb_rx.EOF_POS),
        .RX_SOF          (mfb_rx.SOF    ),
        .RX_EOF          (mfb_rx.EOF    ),
        .RX_SRC_RDY      (mfb_rx.SRC_RDY),
        .RX_DST_RDY      (mfb_rx.DST_RDY),

        .TX_DATA         (mfb_tx.DATA   ),
        .TX_META         (mfb_tx.META   ),
        .TX_SOF_POS      (mfb_tx.SOF_POS),
        .TX_EOF_POS      (mfb_tx.EOF_POS),
        .TX_SOF_MASKED   (mfb_tx.SOF    ),
        .TX_EOF_MASKED   (mfb_tx.EOF    ),
        .TX_SRC_RDY      (mfb_tx.SRC_RDY),
        .TX_DST_RDY      (mfb_tx.DST_RDY),

        // .TX_SOF_UNMASKED (mfb_tx.SOF    ),
        // .TX_EOF_UNMASKED (mfb_tx.EOF    ),
        // .TX_SRC_RDY      (mfb_tx.SRC_RDY),

        // .TX_SOF_ORIGINAL (mfb_tx.SOF    ),
        // .TX_EOF_ORIGINAL (mfb_tx.EOF    ),
        // .TX_SRC_RDY      (mfb_tx.SRC_RDY),

        .TX_MASK         (mvb_rx.DATA   )
    );


endmodule
