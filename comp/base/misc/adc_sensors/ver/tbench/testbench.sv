// testbench.sv
// Copyright (C) 2019 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;


module testbench;

    // ------ Testbench control ------
    logic CLK = 0;
    logic RESET;
    iMi32 MI(CLK, RESET);

    // ------ CLK generation ---------
    always #(CLK_PERIOD/2) CLK = ~CLK;

    // ------ Design Under Test ------
    DUT DUT_U
    (
        .CLK   (CLK),
        .RESET (RESET),
        .MI    (MI)
    );

    // ------ Test -------------------
    TEST TEST_U
    (
        .CLK     (CLK),
        .RESET   (RESET),
        .MI      (MI)
    );

endmodule
