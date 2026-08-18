// property.sv: Properties for the MVB_REORDERING interfaces
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

module mvb_reordering_property #(
    ITEMS,
    ITEM_WIDTH
) (
        input  RESET,
        mvb_if mvb_rx,
        mvb_if mvb_tx
);

    // --------------- //
    // RX MVB property //
    // --------------- //

    mvb_property #(
        .ITEMS      (ITEMS),
        .ITEM_WIDTH (ITEM_WIDTH)
    )
    mvb_rx_property (
        .RESET (RESET),
        .vif   (mvb_rx)
    );

    // ----------------- //
    // TX MVB properties //
    // ----------------- //

    mvb_property #(
        .ITEMS      (ITEMS),
        .ITEM_WIDTH (ITEM_WIDTH)
    )
    mvb_tx_property (
        .RESET (RESET),
        .vif   (mvb_tx)
    );

endmodule
