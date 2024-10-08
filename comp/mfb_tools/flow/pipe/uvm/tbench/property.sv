//-- property.sv: Properties for mfb bus
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): David Beneš <xbenes52@vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

module mfb_pipe_property #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)
    (
        input RESET,
        mfb_if mfb_wr_vif,
        mfb_if mfb_rd_vif
    );

    //Properties
    mfb_property #(
        .REGIONS        (REGIONS),
        .REGION_SIZE    (REGION_SIZE),
        .BLOCK_SIZE     (BLOCK_SIZE),
        .ITEM_WIDTH     (ITEM_WIDTH),
        .META_WIDTH     (META_WIDTH)
    )
    property_rd (
        .RESET          (reset.RESET),
        .vif            (mfb_rd_vif)
    );

    mfb_property #(
        .REGIONS        (REGIONS),
        .REGION_SIZE    (REGION_SIZE),
        .BLOCK_SIZE     (BLOCK_SIZE),
        .ITEM_WIDTH     (ITEM_WIDTH),
        .META_WIDTH     (META_WIDTH)
    )
    property_wr (
        .RESET          (reset.RESET),
        .vif            (mfb_wr_vif)
    );

endmodule

