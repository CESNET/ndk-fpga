// packet_delayer_property.sv: MFB bus properties for the packet delayer
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

// MFB protocol assertions on the RX (with {META, TS}) and TX interfaces
module packet_delayer_property #(
    int unsigned MFB_REGIONS,
    int unsigned MFB_REGION_SIZE,
    int unsigned MFB_BLOCK_SIZE,
    int unsigned MFB_ITEM_WIDTH,
    int unsigned RX_MFB_META_WIDTH,
    int unsigned TX_MFB_META_WIDTH
)
    (
        input RESET,
        mfb_if tx_mfb_vif,
        mfb_if rx_mfb_vif
    );

    mfb_property #(
        .REGIONS      (MFB_REGIONS),
        .REGION_SIZE  (MFB_REGION_SIZE),
        .BLOCK_SIZE   (MFB_BLOCK_SIZE),
        .ITEM_WIDTH   (MFB_ITEM_WIDTH),
        .META_WIDTH   (TX_MFB_META_WIDTH)
    )
    tx_mfb_prop (
        .RESET (RESET),
        .vif   (tx_mfb_vif)
    );

    mfb_property #(
        .REGIONS      (MFB_REGIONS),
        .REGION_SIZE  (MFB_REGION_SIZE),
        .BLOCK_SIZE   (MFB_BLOCK_SIZE),
        .ITEM_WIDTH   (MFB_ITEM_WIDTH),
        .META_WIDTH   (RX_MFB_META_WIDTH)
    )
    rx_mfb_prop (
        .RESET (RESET),
        .vif   (rx_mfb_vif)
    );

endmodule
