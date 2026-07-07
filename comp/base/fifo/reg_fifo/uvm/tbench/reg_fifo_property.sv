// property.sv: Properties for MVB buses
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

module reg_fifo_property #(DATA_WIDTH) (
        input  RESET,
        mvb_if mvb_rx,
        mvb_if mvb_tx
);

    mvb_property #(
        .ITEMS      (1         ),
        .ITEM_WIDTH (DATA_WIDTH)
    )
    mvb_rx_prop (
        .RESET (RESET ),
        .vif   (mvb_rx)
    );

    mvb_property #(
        .ITEMS      (1         ),
        .ITEM_WIDTH (DATA_WIDTH)
    )
    mvb_tx_prop (
        .RESET (RESET ),
        .vif   (mvb_tx)
    );
endmodule
