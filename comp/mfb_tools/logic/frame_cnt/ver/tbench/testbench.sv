/*!
 * \file testbench.sv
 * \brief Testbench
 * \author Daniel Kriz <xkrizd01@vutbr.cz>
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
    logic[CNT_WIDTH-1 : 0] FRAME_COUNTER;
    iMfbRx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH,CNT_WIDTH) RX(CLK, RESET);
    iMfbTx #(REGIONS,REGION_SIZE,BLOCK_SIZE,ITEM_WIDTH,CNT_WIDTH) TX(CLK, RESET);

    always #(CLK_PERIOD/2) CLK = ~CLK;

    DUT DUT_U (
        .CLK     (CLK),
        .RESET   (RESET),
        .FRAME_COUNTER (FRAME_COUNTER),
        .RX      (RX),
        .TX      (TX)
    );

    TEST TEST_U (
        .CLK     (CLK),
        .RESET   (RESET),
        .FRAME_COUNTER (FRAME_COUNTER),
        .RX      (RX),
        .TX      (TX),
        .MONITOR (TX)
    );

endmodule
