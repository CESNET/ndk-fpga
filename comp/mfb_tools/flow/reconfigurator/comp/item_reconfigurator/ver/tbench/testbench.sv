// testbench.sv: Top Entity for automatic test
// Copyright (C) 2020 CESNET
// Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;

module testbench;

    logic CLK = 0;
    logic RESET;
    iMfbRx #(REGIONS,REGION_SIZE,RX_BLOCK_SIZE,RX_ITEM_WIDTH,META_WIDTH) RX(CLK, RESET);
    iMfbTx #(REGIONS,REGION_SIZE,TX_BLOCK_SIZE,RX_ITEM_WIDTH*RX_BLOCK_SIZE/TX_BLOCK_SIZE,META_WIDTH) TX(CLK, RESET);

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

