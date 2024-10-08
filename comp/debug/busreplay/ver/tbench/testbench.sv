/*!
 * \file testbench.sv
 * \brief Testbench
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import test_pkg::*; // Test constants



module testbench;

    logic CLK = 0;
    logic RESET;
    iFrameLinkURx #(DATA_WIDTH, EOP_POS_WIDTH, SOP_POS_WIDTH) RX (CLK, RESET);
    iFrameLinkUTx #(DATA_WIDTH, EOP_POS_WIDTH, SOP_POS_WIDTH) TX (CLK, RESET);
    iMi32 MI_DUMP (CLK, RESET);
    iMi32 MI_REPLAY (CLK, RESET);


    //-- Clock generation -----------------------------------------------------
    always #(10ns/2) CLK = ~CLK;


    //-- Design Under Test ----------------------------------------------------
    DUT DUT_U (
        .CLK       (CLK),
        .RESET     (RESET),
        .RX        (RX),
        .TX        (TX),
        .MI_DUMP   (MI_DUMP),
        .MI_REPLAY (MI_REPLAY)
    );


    //-- Test -----------------------------------------------------------------
    TEST TEST_U (
        .RESET     (RESET),
        .RX        (RX),
        .TX        (TX),
        .MI_DUMP   (MI_DUMP),
        .MI_REPLAY (MI_REPLAY)
    );

endmodule : testbench
