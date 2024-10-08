// testbench.sv
// Copyright (C) 2020 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;

module testbench;

    logic RX_CLK = 0;
    logic TX_CLK = 0;
    logic RX_RST;
    logic TX_RST;
    logic RESET;

    iMvbRx #(1,DATA_WIDTH) RX(RX_CLK, RX_RST);
    iMvbTx #(1,DATA_WIDTH) TX(TX_CLK, TX_RST);

    always #(RX_CLK_PERIOD/2) RX_CLK = ~RX_CLK;
    always #(TX_CLK_PERIOD/2) TX_CLK = ~TX_CLK;

    always @(posedge RX_CLK) RX_RST = RESET;
    always @(posedge TX_CLK) TX_RST = RESET;

    DUT DUT_U (
        .RX_CLK  (RX_CLK),
        .TX_CLK  (TX_CLK),
        .RX_RST  (RX_RST),
        .TX_RST  (TX_RST),
        .RX      (RX),
        .TX      (TX)
    );

    TEST TEST_U (
        .CLK     (RX_CLK),
        .RESET   (RESET),
        .RX      (RX),
        .TX      (TX),
        .MONITOR (TX)
    );

endmodule
