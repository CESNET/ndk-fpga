/*!
 * \file testbench.sv
 * \brief Testbench
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2018
 */
 /*
 * Copyright (C) 2018 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */


module testbench;

    logic RESET;
    logic CLK = 0;
    iMi32 MI (CLK, RESET);


    always #(5ns/2) CLK = ~CLK;


    DUT DUT_U (
        .CLK     (CLK),
        .RESET   (RESET),
        .MI      (MI)
    );

    TEST TEST_U (
        .CLK        (CLK),
        .RESET      (RESET),
        .MI         (MI)
    );

endmodule
