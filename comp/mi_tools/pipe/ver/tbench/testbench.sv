//-- testbench.sv: Testbench
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


import test_pkg::*;



module testbench;

    logic CLK = 0;
    logic RESET;

    iMi #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)  MI_MASTER    (CLK, RESET);
    iMi #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH)  MI_SLAVE   (CLK, RESET);


    always #(CLK_PERIOD/2) CLK = ~CLK;


    DUT DUT_U (
        .CLK        (CLK),
        .RESET      (RESET),
        .MI_MASTER  (MI_MASTER),
        .MI_SLAVE   (MI_SLAVE)
    );

    TEST TEST_U (
        .CLK        (CLK),
        .RESET      (RESET),
        .MI_MASTER  (MI_MASTER),
        .MI_SLAVE   (MI_SLAVE)
    );

endmodule
