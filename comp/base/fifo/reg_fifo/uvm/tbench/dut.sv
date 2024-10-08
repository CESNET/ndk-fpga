// dut.sv: Design under test
// Copyright (C) 2024 CESNET z. s. p. o.
// Author(s): Vladislav Valek <valekv@cesnet.cz>

// SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT (
    input logic CLK,
    input logic RST,
    mvb_if.dut_rx mvb_rx,
    mvb_if.dut_tx mvb_tx
);

    logic mvb_rx_src_rdy;

    REG_FIFO #(
        .DATA_WIDTH (DATA_WIDTH),
        .ITEMS      (ITEMS),
        .FAKE_FIFO  (FAKE_FIFO)
    ) VHDL_DUT_U (
        .CLK        (CLK),
        .RST        (RST),

        .RX_DATA    (mvb_rx.DATA),
        .RX_SRC_RDY (mvb_rx_src_rdy),
        .RX_DST_RDY (mvb_rx.DST_RDY),

        .TX_DATA    (mvb_tx.DATA),
        .TX_SRC_RDY (mvb_tx.SRC_RDY),
        .TX_DST_RDY (mvb_tx.DST_RDY)
    );

    assign mvb_rx_src_rdy = mvb_rx.VLD & mvb_rx.SRC_RDY;
    assign mvb_tx.VLD = 1;
endmodule
