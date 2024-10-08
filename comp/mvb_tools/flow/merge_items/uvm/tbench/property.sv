//-- property.sv: Properties for mvb bus
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

module merge_items_property #(RX0_ITEMS, RX1_ITEMS, RX0_ITEM_WIDTH, RX1_ITEM_WIDTH, TX_ITEM_WIDTH) (
        input  RESET,
        mvb_if mvb_rx0_vif,
        mvb_if mvb_rx1_vif,
        mvb_if mvb_tx_vif,
        mvb_if mvb_tx0_vif,
        mvb_if mvb_tx1_vif
);

    mvb_property #(
        .ITEMS      (RX0_ITEMS     ),
        .ITEM_WIDTH (RX0_ITEM_WIDTH)
    )
    mvb_rx0_prop (
        .RESET (RESET      ),
        .vif   (mvb_rx0_vif)
    );

    mvb_property #(
        .ITEMS      (RX1_ITEMS     ),
        .ITEM_WIDTH (RX1_ITEM_WIDTH)
    )
    mvb_rx1_prop (
        .RESET (RESET      ),
        .vif   (mvb_rx1_vif)
    );

    mvb_property #(
        .ITEMS      (RX0_ITEMS    ),
        .ITEM_WIDTH (TX_ITEM_WIDTH)
    )
    mvb_tx_prop (
        .RESET (RESET     ),
        .vif   (mvb_tx_vif)
    );

    mvb_property #(
        .ITEMS      (RX0_ITEMS     ),
        .ITEM_WIDTH (RX0_ITEM_WIDTH)
    )
    mvb_tx0_prop (
        .RESET (RESET     ),
        .vif   (mvb_tx0_vif)
    );

    mvb_property #(
        .ITEMS      (RX0_ITEMS     ),
        .ITEM_WIDTH (RX1_ITEM_WIDTH)
    )
    mvb_tx1_prop (
        .RESET (RESET     ),
        .vif   (mvb_tx1_vif)
    );

endmodule
