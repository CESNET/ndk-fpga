//-- property.sv: Properties for mfb bus
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Daniel Kříž <danielkriz@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause


module timestamp_limiter_property #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, RX_MFB_META_WIDTH, TX_MFB_META_WIDTH)
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
