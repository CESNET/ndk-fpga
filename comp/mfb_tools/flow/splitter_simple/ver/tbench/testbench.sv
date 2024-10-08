/*!
 * \file testbench.sv
 * \brief Testbench
 * \author Daniel Kondys <xkondy00@vutbr.cz>
 * \date 2019
 */
 /*
 * Copyright (C) 2019 CESNET z. s. p. o.
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
    iMfbRx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) RX(CLK, RESET);
    iMfbTx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) TX0(CLK, RESET);
    iMfbTx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) TX1(CLK, RESET);


    always #(CLK_PERIOD/2) CLK = ~CLK;


    DUT DUT_U (
        .CLK     (CLK),
        .RESET   (RESET),
        .RX      (RX),
        .TX0     (TX0),
        .TX1     (TX1)
    );

    TEST TEST_U (
        .CLK      (CLK),
        .RESET    (RESET),
        .RX       (RX),
        .TX0      (TX0),
        .TX1      (TX1),
        .MONITOR0 (TX0),
        .MONITOR1 (TX1)
    );

endmodule
