// property.sv: Properties for mfb bus
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


module dut_property #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH)
    (
        input RX_RESET,
        input TX_RESET,
        mfb_if tx_mfb_vif,
        mfb_if rx_mfb_vif,
        mvb_if mvb_vif
    );

    mfb_property #(
        .REGIONS      (MFB_REGIONS),
        .REGION_SIZE  (MFB_REGION_SIZE),
        .BLOCK_SIZE   (MFB_BLOCK_SIZE),
        .ITEM_WIDTH   (MFB_ITEM_WIDTH),
        .META_WIDTH   (MFB_META_WIDTH)
    )
    tx_mfb_prop (
        .RESET (TX_RESET),
        .vif   (tx_mfb_vif)
    );

    mfb_property #(
        .REGIONS      (MFB_REGIONS),
        .REGION_SIZE  (MFB_REGION_SIZE),
        .BLOCK_SIZE   (MFB_BLOCK_SIZE),
        .ITEM_WIDTH   (MFB_ITEM_WIDTH),
        .META_WIDTH   (MFB_META_WIDTH)
    )
    rx_mfb_prop (
        .RESET (RX_RESET),
        .vif   (rx_mfb_vif)
    );

    mvb_property #(
        .ITEMS      (MFB_REGIONS),
        .ITEM_WIDTH (MFB_META_WIDTH)
    )
    mvb_prop (
        .RESET (TX_RESET),
        .vif   (mvb_vif)
    );

endmodule
