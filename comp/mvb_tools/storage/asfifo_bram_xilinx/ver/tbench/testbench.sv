/*!
 * \file testbench.sv
 * \brief Testbench
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET z. s. p. o.
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
    iMvbRx #(REGIONS,ITEM_WIDTH) RX(RX_CLK, RESET);
    logic TX_CLK = 0;
    iMvbTx #(REGIONS,ITEM_WIDTH) TX(TX_CLK, RESET);


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
        .MONITOR (TX)
    );

endmodule
