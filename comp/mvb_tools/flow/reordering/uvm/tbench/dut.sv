// dut.sv: Design Under Test
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
// SPDX-License-Identifier: BSD-3-Clause

module dut #(
    int unsigned ITEMS,
    int unsigned ITEM_WIDTH,
    bit OUT_REG_EN,
    bit REORDERING_EN
)
(
    input logic CLK,
    input logic RST,
    mvb_if.dut_rx mvb_rx,
    mvb_if.dut_tx mvb_tx
);

    // KEY_WIDTH is at least 1
    localparam int unsigned KEY_WIDTH = ($clog2(ITEMS) == 0) ? 1 : $clog2(ITEMS);

    logic [ITEMS*KEY_WIDTH-1:0] keys;
    logic [ITEMS*ITEM_WIDTH-1:0]    data;

    generate
        for (genvar it = 0; it < ITEMS; it++) begin : gen_i
            assign {keys[(it+1)*KEY_WIDTH-1 -: KEY_WIDTH], data[(it+1)*ITEM_WIDTH-1 -: ITEM_WIDTH]}
            = mvb_rx.DATA[(it+1)*(ITEM_WIDTH + KEY_WIDTH)-1    -: (ITEM_WIDTH + KEY_WIDTH)];
        end
    endgenerate

    // Wrapper ensures REORDER_KEY port is at least 1 bit wide
    MVB_REORDERING_WRAPPER  #(
        .ITEMS     (ITEMS),
        .ITEM_WIDTH (ITEM_WIDTH),
        .OUT_REG_EN  (OUT_REG_EN),
        .REORDERING_EN  (REORDERING_EN)
    ) VHDL_DUT_U (
        .CLK   (CLK),
        .RESET (RST),

        .RX_DATA    (data),
        .RX_VLD     (mvb_rx.VLD),
        .RX_SRC_RDY (mvb_rx.SRC_RDY),
        .RX_DST_RDY (mvb_rx.DST_RDY),

        .TX_DATA    (mvb_tx.DATA),
        .TX_VLD     (mvb_tx.VLD),
        .TX_SRC_RDY (mvb_tx.SRC_RDY),
        .TX_DST_RDY (mvb_tx.DST_RDY),

        .REORDER_KEY (keys)

    );

endmodule
