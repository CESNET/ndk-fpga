// testbench.sv: Top Entity for automatic test
// Copyright (C) 2023 CESNET z. s. p. o.
// Author: Tomas Fukac <fukac@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;

module testbench;

    logic CLK = 0;
    logic RESET;

    iWbRx  #(DATA_WIDTH, ADDR_WIDTH     ) WRITE     (CLK, RESET);
    iMvbRx #(1,          ADDR_WIDTH     ) READ      (CLK, RESET);
    iMvbTx #(1,          2*DATA_WIDTH   ) READ_OUT  (CLK, RESET);
    iMvbRx #(MVB_ITEMS,  DATA_WIDTH     ) MATCH     (CLK, RESET);
    iMvbTx #(MVB_ITEMS,  ITEMS+1        ) MATCH_OUT (CLK, RESET);

    always #(CLK_PERIOD/2) CLK = ~CLK;

    DUT DUT_U (
        .CLK       (CLK),
        .RESET     (RESET),
        .WRITE     (WRITE),
        .READ      (READ),
        .READ_OUT  (READ_OUT),
        .MATCH     (MATCH),
        .MATCH_OUT (MATCH_OUT)
    );

    TEST TEST_U (
        .CLK           (CLK),
        .RESET         (RESET),
        .WRITE         (WRITE),
        .READ          (READ),
        .READ_OUT      (READ_OUT),
        .MATCH         (MATCH),
        .MATCH_OUT     (MATCH_OUT),
        .READ_MONITOR  (READ_OUT),
        .MATCH_MONITOR (MATCH_OUT)
    );

endmodule
