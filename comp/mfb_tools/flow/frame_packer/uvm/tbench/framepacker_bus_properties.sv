// property.sv: Properties for MFB & MVB bus
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): David Beneš <xbenes52@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

module framepacker_bus_properties #(MFB_REGIONS, MFB_REGION_SIZE, MFB_BLOCK_SIZE, MFB_ITEM_WIDTH, MFB_META_WIDTH, MVB_ITEMS, MVB_ITEM_WIDTH)
    (
        input RESET,
        mfb_if mfb_wr_vif,
        mfb_if mfb_rd_vif,
        mvb_if mvb_wr_vif,
        mvb_if mvb_rd_vif
    );

    //MFB Properties
    mfb_property #(
        .REGIONS        (MFB_REGIONS),
        .REGION_SIZE    (MFB_REGION_SIZE),
        .BLOCK_SIZE     (MFB_BLOCK_SIZE),
        .ITEM_WIDTH     (MFB_ITEM_WIDTH),
        .META_WIDTH     (MFB_META_WIDTH)
    )
    mfb_property_rd (
        .RESET          (reset.RESET),
        .vif            (mfb_rd_vif)
    );
    mfb_property #(
        .REGIONS        (MFB_REGIONS),
        .REGION_SIZE    (MFB_REGION_SIZE),
        .BLOCK_SIZE     (MFB_BLOCK_SIZE),
        .ITEM_WIDTH     (MFB_ITEM_WIDTH),
        .META_WIDTH     (MFB_META_WIDTH)
    )
    mfb_property_wr (
        .RESET          (reset.RESET),
        .vif            (mfb_wr_vif)
    );

    //MVB Properties
    mvb_property #(
        .ITEMS          (MVB_ITEMS),
        .ITEM_WIDTH     (MVB_ITEM_WIDTH)
    )
    mvb_property_rd(
        .RESET          (reset.RESET),
        .vif            (mvb_rd_vif)
    );
    mvb_property  #(
        .ITEMS          (MVB_ITEMS),
        .ITEM_WIDTH     (MVB_ITEM_WIDTH)
    )
    mvb_property_wr (
        .RESET          (reset.RESET),
        .vif            (mvb_wr_vif)
    );

endmodule
