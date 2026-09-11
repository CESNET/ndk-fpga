/*!
 * \file testbench.sv
 * \brief Testbench
 * \author Jakub Cabal <xcabal05@stud.feec.vutbr.cz>
 * \date 2017
 */
 /*
 * Copyright (C) 2017 CESNET z. s. p. o.
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

    iMfbRx #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH,MFB_META_WIDTH) RX_MFB[MERGER_INPUTS] (CLK, RESET);
    iMfbTx #(MFB_REGIONS,MFB_REGION_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH,MFB_META_WIDTH) TX_MFB(CLK, RESET);

    always #(CLK_PERIOD/2) CLK = ~CLK;

    DUT DUT_U (
        .CLK    (CLK   ),
        .RESET  (RESET ),
        .RX_MFB (RX_MFB),
        .TX_MFB (TX_MFB)
    );

    TEST TEST_U (
        .CLK     (CLK   ),
        .RESET   (RESET ),
        .RX_MFB  (RX_MFB),
        .TX_MFB  (TX_MFB),
        .MONITOR (TX_MFB)
    );

endmodule
