// testbench.sv: Top Entity for automatic test
// Copyright (C) 2020 CESNET
// Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;



module testbench;

    logic CLK = 0;
    logic RESET;
    iMfbRx #(RX_REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) RX(CLK, RESET);
    iMfbTx #(TX_REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) TX(CLK, RESET);


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

