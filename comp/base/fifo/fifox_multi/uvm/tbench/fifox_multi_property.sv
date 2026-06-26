// property.sv: Properties for MVB buses
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

module fifox_multi_property #(DATA_WIDTH, WRITE_PORTS) (
        input  RESET,
        mvb_if mvb_rx
);

    mvb_property #(
        .ITEMS      (WRITE_PORTS),
        .ITEM_WIDTH (DATA_WIDTH )
    )
    mvb_rx_prop (
        .RESET (RESET ),
        .vif   (mvb_rx)
    );

endmodule
