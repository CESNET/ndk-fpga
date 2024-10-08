// property.sv: Properties for DUT
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


module dut_property #(RX_MFB_REGIONS, RX_MFB_REGION_S, RX_MFB_BLOCK_S, RX_MFB_ITEM_W, TX_MFB_REGIONS, TX_MFB_REGION_S, TX_MFB_BLOCK_S, TX_MFB_ITEM_W, RX_MVB_ITEM_W, USERMETA_W)
    (
        input RESET,
        mfb_if rx_mfb_vif,
        mfb_if tx_mfb_vif,
        mvb_if rx_mvb_vif,
        mvb_if tx_mvb_vif
    );

    mfb_property #(
        .REGIONS      (TX_MFB_REGIONS),
        .REGION_SIZE  (TX_MFB_REGION_S),
        .BLOCK_SIZE   (TX_MFB_BLOCK_S),
        .ITEM_WIDTH   (TX_MFB_ITEM_W),
        .META_WIDTH   (USERMETA_W)
    )
    tx_mfb_prop (
        .RESET (RESET),
        .vif   (tx_mfb_vif)
    );

    mfb_property #(
        .REGIONS      (RX_MFB_REGIONS),
        .REGION_SIZE  (RX_MFB_REGION_S),
        .BLOCK_SIZE   (RX_MFB_BLOCK_S),
        .ITEM_WIDTH   (RX_MFB_ITEM_W),
        .META_WIDTH   (USERMETA_W)
    )
    rx_mfb_prop (
        .RESET (RESET),
        .vif   (rx_mfb_vif)
    );

    mvb_property #(
        .ITEMS      (RX_MFB_REGIONS),
        .ITEM_WIDTH (RX_MVB_ITEM_W)
    )
    rx_mvb_prop (
        .RESET (RESET),
        .vif   (rx_mvb_vif)
    );

    mvb_property #(
        .ITEMS      (TX_MFB_REGIONS),
        .ITEM_WIDTH (USERMETA_W)
    )
    tx_mvb_prop (
        .RESET (RESET),
        .vif   (tx_mvb_vif)
    );

endmodule
