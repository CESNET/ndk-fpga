// file testbench.sv: Testbench
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kondys <xkondy00@vutbr.cz>
//
// SPDX-License-Identifier: BSD-3-Clause


import test_pkg::*;

module testbench;

    logic CLK = 0;
    logic RESET;
    iMfbRx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) RX(CLK, RESET);
    iMfbTx #(TX_REGIONS,TX_REGION_SIZE,TX_BLOCK_SIZE,TX_ITEM_WIDTH) TX(CLK, RESET);

    always #(CLK_PERIOD/2) CLK = ~CLK;

    DUT DUT_U (
        .CLK     (CLK),
        .RESET   (RESET),
        .RX      (RX),
        .TX      (TX)
    );

    TEST TEST_U (
        .CLK     (CLK),
        .RESET   (RESET),
        .RX      (RX),
        .TX      (TX),
        .MONITOR (TX)
    );

endmodule
