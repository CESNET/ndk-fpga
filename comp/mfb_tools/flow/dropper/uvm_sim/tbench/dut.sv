//-- dut.sv: Design under test
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author:   Daniel Kříž <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT (
    input logic     CLK,
    input logic     RST,
    mfb_if.dut_rx   mfb_rx,
    mfb_if.dut_tx   mfb_tx
    );

    logic [REGIONS*META_WIDTH-1 : 0] meta;
    logic [REGIONS-1 : 0]            drop;

    generate
        for (genvar r = 0; r < REGIONS; r++) begin
            assign meta[(r+1)*META_WIDTH-1 : r*META_WIDTH] = mfb_rx.META[(r+1)*META_WIDTH+r-1 : r*META_WIDTH+r];
            assign drop[r]                                 = mfb_rx.META[(r+1)*META_WIDTH+r];
        end
    endgenerate

    MFB_DROPPER #(
        .REGIONS          (REGIONS),
        .REGION_SIZE      (REGION_SIZE),
        .BLOCK_SIZE       (BLOCK_SIZE),
        .ITEM_WIDTH       (ITEM_WIDTH),
        .META_WIDTH       (META_WIDTH)
    ) VHDL_DUT_U (
        .CLK        (CLK),
        .RESET      (RST),

        .RX_DATA    (mfb_rx.DATA),
        .RX_META    (meta),
        .RX_SOF_POS (mfb_rx.SOF_POS),
        .RX_EOF_POS (mfb_rx.EOF_POS),
        .RX_SOF     (mfb_rx.SOF),
        .RX_EOF     (mfb_rx.EOF),
        .RX_SRC_RDY (mfb_rx.SRC_RDY),
        .RX_DST_RDY (mfb_rx.DST_RDY),
        .RX_DROP    (drop),

        .TX_DATA    (mfb_tx.DATA),
        .TX_META    (mfb_tx.META),
        .TX_SOF_POS (mfb_tx.SOF_POS),
        .TX_EOF_POS (mfb_tx.EOF_POS),
        .TX_SOF     (mfb_tx.SOF),
        .TX_EOF     (mfb_tx.EOF),
        .TX_SRC_RDY (mfb_tx.SRC_RDY),
        .TX_DST_RDY (mfb_tx.DST_RDY)

    );


endmodule
