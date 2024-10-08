/*!
 * \file testbench.sv
 * \brief Testbench
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
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
    iFrameLinkRx #(DATA_WIDTH,DREM_WIDTH) RX(CLK, RESET);
    iFrameLinkTx #(DATA_WIDTH,DREM_WIDTH) TX(CLK, RESET);
    // iFrameLinkUFifo #(STATUS_WIDTH) CTRL(CLK, RESET);


    always #(CLK_PERIOD/2) CLK = ~CLK;


    DUT DUT_U (
        .CLK     (CLK),
        .RESET   (RESET),
        .RX      (RX),
        .TX      (TX) //,
        // .CTRL    (CTRL)
    );

    TEST TEST_U (
        .CLK     (CLK),
        .RESET   (RESET),
        .RX      (RX),
        .TX      (TX),
        // .CTRL    (CTRL),
        .MONITOR_TX (TX)
    );

endmodule

