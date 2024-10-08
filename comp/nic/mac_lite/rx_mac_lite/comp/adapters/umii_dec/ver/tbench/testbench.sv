// testbench.sv
// Copyright (C) 2019 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;

module testbench;

    logic ASYNC_RESET;
    logic CLK = 0;
    logic RESET;

    iMiiRx #(MII_DATA_WIDTH)                            MII (CLK, RESET);
    iMfbTx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) MFB (CLK, RESET);

    always #(CLK_PERIOD/2) CLK   = ~CLK;
    always @(posedge CLK)  RESET = ASYNC_RESET;

    DUT DUT_U (
        .CLK   (CLK),
        .RESET (RESET),
        .MII   (MII),
        .MFB   (MFB)
    );

    TEST TEST_U (
        .CLK         (CLK),
        .ASYNC_RESET (ASYNC_RESET),
        .MII         (MII),
        .MFB         (MFB),
        .MFB_MONITOR (MFB)
    );

endmodule
