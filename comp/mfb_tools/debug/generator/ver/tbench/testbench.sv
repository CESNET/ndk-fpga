// testbench.sv
// Copyright (C) 2020 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;

module testbench;

    logic CLK = 0;
    logic RESET;

    iMfbTx #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH) TX   (CLK, RESET);
    iMi32                                                               MI32 (CLK, RESET);

    always #(CLK_PERIOD/2) CLK = ~CLK;

    DUT DUT_U (
        .CLK   (CLK),
        .RESET (RESET),
        .MI32  (MI32),
        .TX    (TX)
    );

    TEST TEST_U (
        .CLK     (CLK),
        .RESET   (RESET),
        .TX      (TX),
        .MONITOR (TX),
        .MI32    (MI32)
    );

endmodule
