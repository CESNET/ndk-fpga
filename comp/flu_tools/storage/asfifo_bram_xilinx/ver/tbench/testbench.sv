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

    logic RESET;
    logic RX_CLK = 0;
    iFrameLinkURx #(DATA_WIDTH,EOP_POS_WIDTH,SOP_POS_WIDTH) RX(RX_CLK, RESET);
    logic TX_CLK = 0;
    iFrameLinkUTx #(DATA_WIDTH,EOP_POS_WIDTH,SOP_POS_WIDTH) TX(TX_CLK, RESET);


    always #(RX_CLK_PERIOD/2) RX_CLK = ~RX_CLK;
    always #(TX_CLK_PERIOD/2) TX_CLK = ~TX_CLK;


    DUT DUT_U (
        .RESET   (RESET),
        .RX_CLK  (RX_CLK),
        .RX      (RX),
        .TX_CLK  (TX_CLK),
        .TX      (TX)
    );

    TEST TEST_U (
        .RESET   (RESET),
        .RX_CLK  (RX_CLK),
        .RX      (RX),
        .TX_CLK  (TX_CLK),
        .TX      (TX),
        .MONITOR_TX (TX)
    );

endmodule

