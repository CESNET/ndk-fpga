// property.sv: Properties for MVB_MERGE_STREAMS interfaces
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

module mvb_merge_streams_property #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS) (
        input  RESET,
        mvb_if mvb_rx[RX_STREAMS],
        mvb_if mvb_tx
);

    // ----------------- //
    // RX MVB properties //
    // ----------------- //

    generate;
        for (genvar i = 0; i < RX_STREAMS; i++) begin : gen_i
            mvb_property #(
                .ITEMS      (MVB_ITEMS),
                .ITEM_WIDTH (MVB_ITEM_WIDTH)
            )
            mvb_rx_property (
                .RESET (RESET),
                .vif   (mvb_rx[i])
            );
        end
    endgenerate

    // --------------- //
    // TX MVB property //
    // --------------- //

    mvb_property #(
        .ITEMS      (MVB_ITEMS),
        .ITEM_WIDTH (MVB_ITEM_WIDTH)
    )
    mvb_rx_property (
        .RESET (RESET),
        .vif   (mvb_tx)
    );

endmodule
