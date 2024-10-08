// crossbarx_stream.vhd: Crossbarx stream
// Copyright (C) 2020 CESNET z. s. p. o.
// Author(s): Daniel Kriz <xkrizd01@vutbr.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;

module testbench;

    logic ASYNC_RESET;
    logic RX_CLK = 0;
    logic RX_CLK2 = 0;
    logic RX_RESET;
    logic TX_CLK = 0;
    logic TX_RESET;
    logic CX_CLK_ARB = 0;
    logic CX_RESET_ARB;
    iMfbRx #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH,EXT_META_WIDTH) RX(RX_CLK, RX_RESET);
    iMfbTx #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH,MFB_META_WIDTH) TX(TX_CLK, TX_RESET);

    always #(RX_CLK_PERIOD/2)  RX_CLK     = ~RX_CLK;
    always #(RX_CLK_PERIOD/4)  RX_CLK2    = ~RX_CLK2;
    always #(CLK_ARB_PERIOD/2) CX_CLK_ARB = ~CX_CLK_ARB;

    if (OBUF_META_EQ_OUTPUT == 1)
        always #(RX_CLK_PERIOD/2)   TX_CLK      = RX_CLK;
    else if (OBUF_INPUT_EQ_OUTPUT==1) begin
        if (CX_USE_CLK_ARB == 1)
            always #(CLK_ARB_PERIOD/2)  TX_CLK  = CX_CLK_ARB;
        else if (CX_USE_CLK2 == 1)
            always #(RX_CLK_PERIOD/4) TX_CLK    = RX_CLK2;
        else
            always #(RX_CLK_PERIOD/2)   TX_CLK  = RX_CLK;
    end else
        always #(TX_CLK_PERIOD/2)   TX_CLK      = ~TX_CLK;

    always @(posedge RX_CLK) RX_RESET         = ASYNC_RESET;
    always @(posedge TX_CLK) TX_RESET         = ASYNC_RESET;
    always @(posedge CX_CLK_ARB) CX_RESET_ARB = ASYNC_RESET;

    DUT DUT_U (
        .RX_CLK       (RX_CLK),
        .RX_CLK2      (RX_CLK2),
        .RX_RESET     (RX_RESET),
        .TX_RESET     (TX_RESET),
        .TX_CLK       (TX_CLK),
        .CX_CLK_ARB   (CX_CLK_ARB),
        .CX_RESET_ARB (CX_RESET_ARB),
        .RX           (RX),
        .TX           (TX)
    );

    TEST TEST_U (
        .RX_CLK       (RX_CLK),
        .RX_CLK2      (RX_CLK2),
        .TX_CLK       (TX_CLK),
        .CX_CLK_ARB   (CX_CLK_ARB),
        .ASYNC_RESET  (ASYNC_RESET),
        .RX           (RX),
        .TX           (TX),
        .MONITOR      (TX)
    );

endmodule
