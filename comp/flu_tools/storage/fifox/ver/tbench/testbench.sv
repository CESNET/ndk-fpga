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
    iFrameLinkURx #(DATA_WIDTH,EOP_POS_WIDTH,SOP_POS_WIDTH) RX(CLK, RESET);
    iFrameLinkUTx #(DATA_WIDTH,EOP_POS_WIDTH,SOP_POS_WIDTH) TX(CLK, RESET);
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
        .MONITOR_RX (RX),
        .MONITOR_TX (TX)
    );

endmodule

