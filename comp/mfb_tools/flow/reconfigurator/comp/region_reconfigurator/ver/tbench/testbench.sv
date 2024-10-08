// testbench.sv: Top Entity for automatic test
// Copyright (C) 2020 CESNET
// Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;

module testbench;

    logic CLK = 0;
    logic RESET;
    iMfbRx #(RX_REGIONS,RX_REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH,META_WIDTH) RX(CLK, RESET);
    iMfbTx #(TX_REGIONS,RX_REGION_SIZE*RX_REGIONS/TX_REGIONS,BLOCK_SIZE,ITEM_WIDTH,META_WIDTH) TX(CLK, RESET);

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

