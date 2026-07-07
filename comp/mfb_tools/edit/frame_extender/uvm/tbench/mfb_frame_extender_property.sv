// property.sv: Properties for the MFB_FRAME_EXTENDER interfaces
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

module mfb_frame_extender_property #(
    MFB_REGIONS,
    MFB_REGION_SIZE,
    MFB_BLOCK_SIZE,
    MFB_ITEM_WIDTH,
    USERMETA_WIDTH,
    RX_MVB_ITEM_WIDTH
) (
        input  RESET,
        mfb_if mfb_rx,
        mvb_if mvb_rx,
        mfb_if mfb_tx,
        mvb_if mvb_tx
);

    // --------------- //
    // RX MFB property //
    // --------------- //

    mfb_property #(
        .REGIONS     (MFB_REGIONS),
        .REGION_SIZE (MFB_REGION_SIZE),
        .BLOCK_SIZE  (MFB_BLOCK_SIZE),
        .ITEM_WIDTH  (MFB_ITEM_WIDTH),
        .META_WIDTH  (0)
    )
    mfb_rx_prop (
        .RESET (RESET),
        .vif   (mfb_rx)
    );

    // --------------- //
    // RX MVB property //
    // --------------- //

    mvb_property #(
        .ITEMS      (MFB_REGIONS),
        .ITEM_WIDTH (RX_MVB_ITEM_WIDTH)
    )
    mvb_rx_property (
        .RESET (RESET),
        .vif   (mvb_rx)
    );

    // ----------------- //
    // TX MFB properties //
    // ----------------- //

    mfb_property #(
        .REGIONS     (MFB_REGIONS),
        .REGION_SIZE (MFB_REGION_SIZE),
        .BLOCK_SIZE  (MFB_BLOCK_SIZE),
        .ITEM_WIDTH  (MFB_ITEM_WIDTH),
        .META_WIDTH  (USERMETA_WIDTH)
    )
    mfb_tx_property (
        .RESET (RESET),
        .vif   (mfb_tx)
    );

    // ----------------- //
    // TX MVB properties //
    // ----------------- //

    mvb_property #(
        .ITEMS      (MFB_REGIONS),
        .ITEM_WIDTH (USERMETA_WIDTH)
    )
    mvb_tx_property (
        .RESET (RESET),
        .vif   (mvb_tx)
    );

endmodule
