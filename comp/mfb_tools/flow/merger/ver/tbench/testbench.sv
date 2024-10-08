/*!
 * \file testbench.sv
 * \brief Testbench
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2018
 */
 /*
 * Copyright (C) 2018 CESNET z. s. p. o.
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

    iMvbRx #(MVB_ITEMS,MVB_ITEM_WIDTH)                                              RX_MVB[MERGER_INPUTS-1:0] (CLK, RESET);
    iMfbRx #(MFB_REGIONS,MFB_REG_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH,MFB_META_WIDTH) RX_MFB[MERGER_INPUTS-1:0] (CLK, RESET);
    iMvbTx #(MVB_ITEMS,MVB_ITEM_WIDTH)                                              TX_MVB(CLK, RESET);
    iMfbTx #(MFB_REGIONS,MFB_REG_SIZE,MFB_BLOCK_SIZE,MFB_ITEM_WIDTH,MFB_META_WIDTH) TX_MFB(CLK, RESET);

    always #(CLK_PERIOD/2) CLK = ~CLK;

    DUT DUT_U (
       .CLK    (CLK   ),
       .RESET  (RESET ),
       .RX_MVB (RX_MVB),
       .RX_MFB (RX_MFB),
       .TX_MVB (TX_MVB),
       .TX_MFB (TX_MFB)
    );

    TEST TEST_U (
       .CLK    (CLK   ),
       .RESET  (RESET ),
       .RX_MVB (RX_MVB),
       .RX_MFB (RX_MFB),
       .TX_MVB (TX_MVB),
       .TX_MFB (TX_MFB),
       .MO_MVB (TX_MVB),
       .MO_MFB (TX_MFB)
    );

endmodule
