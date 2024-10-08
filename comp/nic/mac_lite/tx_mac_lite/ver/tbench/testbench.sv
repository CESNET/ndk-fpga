// testbench.sv
// Copyright (C) 2019 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;

module testbench;

    logic RX_CLK = 1;
    logic RX_CLK_X2 = 1;
    logic RX_RESET;
    logic TX_CLK = 0;
    logic TX_RESET;
    logic MI_CLK = 0;
    logic MI_RESET;

    iMfbRx #(RX_REGIONS,RX_REGION_SIZE,RX_BLOCK_SIZE,RX_ITEM_WIDTH) RX   (RX_CLK, RX_RESET);
    iMfbTx #(TX_REGIONS,TX_REGION_SIZE,TX_BLOCK_SIZE,TX_ITEM_WIDTH) TX   (TX_CLK, TX_RESET);
    iMi32                                                           MI32 (MI_CLK, MI_RESET);

    always #(RX_CLK_PERIOD/2) RX_CLK = ~RX_CLK;
    always #(RX_CLK_PERIOD/4) RX_CLK_X2 = ~RX_CLK_X2;
    always #(TX_CLK_PERIOD/2) TX_CLK = ~TX_CLK;
    always #(MI_CLK_PERIOD/2) MI_CLK = ~MI_CLK;

    DUT DUT_U (
        .RX_CLK    (RX_CLK),
        .RX_CLK_X2 (RX_CLK_X2),
        .RX_RESET  (RX_RESET),
        .TX_CLK    (TX_CLK),
        .TX_RESET  (TX_RESET),
        .MI_CLK    (MI_CLK),
        .MI_RESET  (MI_RESET),
        .MI32      (MI32),
        .RX        (RX),
        .TX        (TX)
    );

    TEST TEST_U (
        .RX_CLK    (RX_CLK),
        .RX_CLK_X2 (RX_CLK_X2),
        .RX_RESET  (RX_RESET),
        .TX_CLK    (TX_CLK),
        .TX_RESET  (TX_RESET),
        .MI_CLK    (MI_CLK),
        .MI_RESET  (MI_RESET),
        .RX        (RX),
        .TX        (TX),
        .MONITOR   (TX),
        .MI32      (MI32)
    );

endmodule
