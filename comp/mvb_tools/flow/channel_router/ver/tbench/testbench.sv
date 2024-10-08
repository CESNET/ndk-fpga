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
    iMi32 MI(CLK,RESET);
    iMvbRx #(ITEMS,NEW_RX_ITEM_WIDTH) RX(CLK, RESET);
    iMvbTx #(ITEMS,NEW_TX_ITEM_WIDTH) TX(CLK, RESET);


    always #(CLK_PERIOD/2) CLK = ~CLK;


    DUT DUT_U (
        .CLK     (CLK),
        .RESET   (RESET),
        .MI      (MI),
        .RX      (RX),
        .TX      (TX)
    );

    TEST TEST_U (
        .CLK     (CLK),
        .RESET   (RESET),
        .MI      (MI),
        .RX      (RX),
        .TX      (TX),
        .MONITOR (TX)
    );

endmodule
