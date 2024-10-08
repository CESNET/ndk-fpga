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

    logic CLK = 1'b0;
    logic RESET;
    iMfbRx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH,META_WIDTH) RX(CLK, RESET);
    iMfbTx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH,META_WIDTH) TX[OUTPUT_PORTS](CLK, RESET);

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
        .TX      (TX)
    );

endmodule
