// testbench.sv
// Copyright (C) 2019 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;

module testbench;

    logic ASYNC_RESET;
    logic RX_CLK = 0;
    logic RX_RESET;
    logic TX_CLK = 0;
    logic TX_RESET;
    logic MI_CLK = 0;
    logic MI_RESET;

    iMfbRx #(RX_REGIONS,RX_REGION_SIZE,RX_BLOCK_SIZE,RX_ITEM_WIDTH) RX_MFB (RX_CLK, RX_RESET);
    iMfbTx #(TX_REGIONS,TX_REGION_SIZE,TX_BLOCK_SIZE,TX_ITEM_WIDTH) TX_MFB (TX_CLK, TX_RESET);
    iMvbTx #(TX_REGIONS,METADATA_WIDTH)                             TX_MVB (TX_CLK, TX_RESET);
    iMi32                                                           MI     (MI_CLK, MI_RESET);

    always #(RX_CLK_PERIOD/2) RX_CLK = ~RX_CLK;
    always #(TX_CLK_PERIOD/2) TX_CLK = ~TX_CLK;
    always #(MI_CLK_PERIOD/2) MI_CLK = ~MI_CLK;

    always @(posedge RX_CLK) RX_RESET = ASYNC_RESET;
    always @(posedge TX_CLK) TX_RESET = ASYNC_RESET;
    always @(posedge MI_CLK) MI_RESET = ASYNC_RESET;

    DUT DUT_U (
        .RX_CLK   (RX_CLK),
        .RX_RESET (RX_RESET),
        .TX_CLK   (TX_CLK),
        .TX_RESET (TX_RESET),
        .MI_CLK   (MI_CLK),
        .MI_RESET (MI_RESET),
        .MI       (MI),
        .RX_MFB   (RX_MFB),
        .TX_MFB   (TX_MFB),
        .TX_MVB   (TX_MVB)
    );

    TEST TEST_U (
        .RX_CLK      (RX_CLK),
        .TX_CLK      (TX_CLK),
        .ASYNC_RESET (ASYNC_RESET),
        .MI          (MI),
        .RX_MFB      (RX_MFB),
        .TX_MFB      (TX_MFB),
        .MFB_MONITOR (TX_MFB),
        .TX_MVB      (TX_MVB),
        .MVB_MONITOR (TX_MVB)
    );

endmodule
