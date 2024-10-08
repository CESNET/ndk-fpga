/*!
 * \file testbench.sv
 * \brief Testbench
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2017
 */
 /*
 * Copyright (C) 2016 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import test_pkg::*;



module testbench;

    logic CLK = 0;
    logic RESET;
    iWordLinkRx #(2*CARRY_WIDTH+1) RX(CLK, RESET);


    always #(CLK_PERIOD/2) CLK = ~CLK;


    DUT DUT_U (
        .CLK     (CLK),
        .RESET   (RESET),
        .RX      (RX)
    );

    TEST TEST_U (
        .CLK     (CLK),
        .RESET   (RESET),
        .RX      (RX)
    );

endmodule
