//-- property.sv: Properties for mfb bus
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Radek Iša <isa@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


module mac_rx_property #(REGIONS, REGION_SIZE, BLOCK_SIZE, ITEM_WIDTH, META_WIDTH)
    (
        input RESET,
        mfb_if mfb_vif
    );

    mfb_property #(
        .REGIONS      (REGIONS),
        .REGION_SIZE  (REGION_SIZE),
        .BLOCK_SIZE   (BLOCK_SIZE),
        .ITEM_WIDTH   (ITEM_WIDTH),
        .META_WIDTH   (META_WIDTH)
    )
    mfb_prop (
        .RESET (RESET),
        .vif   (mfb_vif)
    );

endmodule
