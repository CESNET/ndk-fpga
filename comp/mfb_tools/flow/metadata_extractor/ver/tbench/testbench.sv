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

module testbench;

    logic CLK = 0;
    logic RESET;
    iMfbRx #(test_pkg::MFB_REGIONS,test_pkg::MFB_REGION_SIZE,test_pkg::MFB_BLOCK_SIZE,test_pkg::MFB_ITEM_WIDTH,test_pkg::MFB_META_WIDTH) RX(CLK);
    iMfbTx #(test_pkg::MFB_REGIONS,test_pkg::MFB_REGION_SIZE,test_pkg::MFB_BLOCK_SIZE,test_pkg::MFB_ITEM_WIDTH,test_pkg::MFB_META_WIDTH) TX_MFB(CLK);
    iMvbTx #(test_pkg::MVB_ITEMS,test_pkg::MFB_META_WIDTH) TX_MVB(CLK);

    always #(test_pkg::CLK_PERIOD/2) CLK = ~CLK;

    DUT DUT_U (
        .CLK         (CLK),
        .RESET       (RESET),
        .RX          (RX),
        .TX_MFB      (TX_MFB),
        .TX_MVB      (TX_MVB)
    );

    TEST TEST_U (
        .CLK         (CLK),
        .RESET       (RESET),
        .RX          (RX),
        .TX_MFB      (TX_MFB),
        .TX_MVB      (TX_MVB)
    );

endmodule
