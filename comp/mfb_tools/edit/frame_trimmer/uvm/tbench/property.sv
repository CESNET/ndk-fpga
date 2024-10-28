// property.sv: Properties for the MFB_FRAME_TRIMMER interfaces
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

module mfb_frame_trimmer_property #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH, LEN_WIDTH) (
        input  RESET,
        mfb_if mfb_rx,
        mfb_if mfb_tx
);

    // --------------- //
    // RX MFB property //
    // --------------- //

    mfb_property #(
        .REGIONS     (REGIONS),
        .REGION_SIZE (REGION_SIZE),
        .BLOCK_SIZE  (BLOCK_SIZE),
        .ITEM_WIDTH  (ITEM_WIDTH),
        .META_WIDTH  (META_WIDTH+1+LEN_WIDTH)
    )
    mfb_rx_prop (
        .RESET (RESET),
        .vif   (mfb_rx)
    );

    // ----------------- //
    // TX MFB properties //
    // ----------------- //

    mfb_property #(
        .REGIONS     (REGIONS),
        .REGION_SIZE (REGION_SIZE),
        .BLOCK_SIZE  (BLOCK_SIZE),
        .ITEM_WIDTH  (ITEM_WIDTH),
        .META_WIDTH  (META_WIDTH)
    )
    mfb_tx_prop (
        .RESET (RESET),
        .vif   (mfb_tx)
    );

endmodule
