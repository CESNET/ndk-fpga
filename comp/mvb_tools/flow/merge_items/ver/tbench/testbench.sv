/*!
 * \file testbench.sv
 * \brief Testbench
 * \author Daniel Kříž <xkrizd01@vutbr.cz>
 * \date 2020
 */
 /*
 * Copyright (C) 2020 CESNET z. s. p. o.
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
    iMvbRx #(RX0_ITEMS,RX0_ITEM_WIDTH) RX0(CLK, RESET);
    iMvbRx #(RX1_ITEMS,RX1_ITEM_WIDTH) RX1(CLK, RESET);
    iMvbTx #(RX0_ITEMS,RX0_ITEM_WIDTH+RX1_ITEM_WIDTH) TX(CLK, RESET);

    always #(CLK_PERIOD/2) CLK = ~CLK;

    DUT DUT_U (
        .CLK     (CLK),
        .RESET   (RESET),
        .RX0     (RX0),
        .RX1     (RX1),
        .TX      (TX)
    );

    TEST TEST_U (
        .CLK     (CLK),
        .RESET   (RESET),
        .RX0     (RX0),
        .RX1     (RX1),
        .TX      (TX),
        .MONITOR (TX)
    );

endmodule
