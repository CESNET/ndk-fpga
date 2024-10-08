// property.sv: Properties for MVB buses
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

module fifox_property #(DATA_WIDTH, STATUS_WIDTH) (
        input  RESET,
        mvb_if mvb_rx,
        mvb_if mvb_tx,
        mvb_if mvb_status
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

    mvb_property #(
        .ITEMS      (1             ),
        .ITEM_WIDTH (STATUS_WIDTH+2)
    )
    mvb_status_prop (
        .RESET (RESET     ),
        .vif   (mvb_status)
    );

endmodule
