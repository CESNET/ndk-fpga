// property.sv: Properties for MVB_SHAKEDOWN interfaces
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

module mvb_shakedown_property #(RX_ITEMS, TX_ITEMS, ITEM_WIDTH) (
        input  RESET,
        mvb_if mvb_rx,
        mvb_if mvb_tx[TX_ITEMS]
);

    // --------------- //
    // RX MVB property //
    // --------------- //

    mvb_property #(
        .ITEMS      (RX_ITEMS),
        .ITEM_WIDTH (ITEM_WIDTH)
    )
    mvb_rx_property (
        .RESET (RESET),
        .vif   (mvb_rx)
    );

    // ----------------- //
    // TX MVB properties //
    // ----------------- //

    generate;
        for (genvar i = 0; i < TX_ITEMS; i++) begin
            mvb_property #(
                .ITEMS      (1),
                .ITEM_WIDTH (ITEM_WIDTH)
            )
            mvb_tx_property (
                .RESET (RESET),
                .vif   (mvb_tx[i])
            );
        end
    endgenerate

endmodule
