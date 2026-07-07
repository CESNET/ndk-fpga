// dut.sv: Design Under Test
// Copyright (C) 2025 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

module dut #(
    int unsigned RX_ITEMS,
    int unsigned TX_ITEMS,
    int unsigned ITEM_WIDTH,
    int unsigned SHAKE_PORTS,
    bit USE_MUX_IMPL,
    string DEVICE
)
(
    input logic CLK,
    input logic RST,
    mvb_if.dut_rx mvb_rx,
    mvb_if.dut_tx mvb_tx[TX_ITEMS]
);

    logic [TX_ITEMS*ITEM_WIDTH -1 : 0] tx_mvb_data;
    logic [TX_ITEMS            -1 : 0] tx_mvb_vld;
    logic [TX_ITEMS            -1 : 0] tx_mvb_next;

    MVB_SHAKEDOWN  #(
        .RX_ITEMS     (RX_ITEMS),
        .TX_ITEMS     (TX_ITEMS),
        .ITEM_WIDTH   (ITEM_WIDTH),
        .SHAKE_PORTS  (SHAKE_PORTS),
        .USE_MUX_IMPL (USE_MUX_IMPL),
        .DEVICE       (DEVICE)
    ) VHDL_DUT_U (
        .CLK   (CLK),
        .RESET (RST),

        .RX_DATA    (mvb_rx.DATA),
        .RX_VLD     (mvb_rx.VLD),
        .RX_SRC_RDY (mvb_rx.SRC_RDY),
        .RX_DST_RDY (mvb_rx.DST_RDY),

        .TX_DATA (tx_mvb_data),
        .TX_VLD  (tx_mvb_vld),
        .TX_NEXT (tx_mvb_next)
    );

    generate;
        for (genvar i = 0; i < TX_ITEMS; i++) begin : gen_i
            assign mvb_tx[i].DATA    = tx_mvb_data[ITEM_WIDTH*(i+1)-1 -: ITEM_WIDTH];
            assign mvb_tx[i].VLD     = tx_mvb_vld[i];
            assign mvb_tx[i].SRC_RDY = 1'b1;
            assign tx_mvb_next[i]    = mvb_tx[i].DST_RDY;
        end
    endgenerate

endmodule
