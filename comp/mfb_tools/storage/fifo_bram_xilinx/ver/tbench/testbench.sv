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

    logic CLK = 0;
    logic RESET;
    iMfbRx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) RX(CLK, RESET);
    iMfbTx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH) TX(CLK, RESET);


    always #(CLK_PERIOD/2) CLK = ~CLK;


    DUT DUT_U (
        .CLK     (CLK),
        .RESET   (RESET),
        .RX      (RX),
        .TX      (TX)
    );

    TEST TEST_U (
        .CLK     (CLK),
        .RESET   (RESET),
        .RX      (RX),
        .TX      (TX),
        .MONITOR (TX)
    );

endmodule
