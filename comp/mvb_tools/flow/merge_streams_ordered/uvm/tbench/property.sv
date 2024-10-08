// property.sv: Properties for MVB buses
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

module merge_streams_ordered_property #(MVB_ITEMS, MVB_ITEM_WIDTH, RX_STREAMS) (
        input  RESET,
        mvb_if rx_mvb_vif [RX_STREAMS -1 : 0],
        mvb_if rx_sel_mvb_vif,
        mvb_if tx_mvb_vif
);

    for (genvar port = 0; port < RX_STREAMS; port++) begin
        mvb_property #(
            .ITEMS      (MVB_ITEMS),
            .ITEM_WIDTH (MVB_ITEM_WIDTH)
        ) rx_mvb_prop (
            .RESET (RESET),
            .vif   (rx_mvb_vif[port])
        );
    end

    mvb_property #(
        .ITEMS      (RX_STREAMS*MVB_ITEMS),
        .ITEM_WIDTH ($clog2(RX_STREAMS))
    ) rx_sel_mvb_prop (
        .RESET (RESET),
        .vif   (rx_sel_mvb_vif)
    );

    mvb_property #(
        .ITEMS      (RX_STREAMS*MVB_ITEMS),
        .ITEM_WIDTH (MVB_ITEM_WIDTH)
    ) tx_mvb_prop (
        .RESET (RESET),
        .vif   (tx_mvb_vif)
    );
endmodule
