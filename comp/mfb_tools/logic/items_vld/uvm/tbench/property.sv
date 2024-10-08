//-- property.sv: Properties for mfb bus
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author(s): Daniel Kriz <xkrizd01@vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


module items_valid_property #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, META_WIDTH, MVB_DATA_WIDTH, MVB_ITEMS)
    (
        input RESET,
        mfb_if rx_mfb_vif,
        mvb_if tx_mvb_vif,
        mvb_if end_mvb_vif
    );

    mfb_property #(
        .REGIONS        (MFB_REGIONS),
        .REGION_SIZE    (MFB_REGION_SIZE),
        .BLOCK_SIZE     (MFB_BLOCK_SIZE),
        .ITEM_WIDTH     (MFB_ITEM_WIDTH),
        .META_WIDTH     (META_WIDTH)
    )
    rx_mfb_prop (
        .RESET (RESET),
        .vif   (rx_mfb_vif)
    );

    mvb_property #(
        .ITEMS      (MVB_ITEMS),
        .ITEM_WIDTH (MVB_DATA_WIDTH)
    )
    tx_mvb_prop (
        .RESET (RESET),
        .vif   (tx_mvb_vif)
    );

    mvb_property #(
        .ITEMS      (MVB_ITEMS),
        .ITEM_WIDTH (1)
    )
    end_mvb_prop (
        .RESET (RESET),
        .vif   (end_mvb_vif)
    );

endmodule
