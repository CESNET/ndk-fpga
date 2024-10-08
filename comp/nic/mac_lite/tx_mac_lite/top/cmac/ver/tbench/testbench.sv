/*!
 * \file testbench.sv
 * \brief Testbench
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2017
 */
 /*
 * Copyright (C) 2017 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import test_pkg::*;

module testbench;

    logic FLU_CLK = 0;
    logic FLU_RESET;
    logic CMAC_CLK = 0;
    logic CMAC_RESET;
    logic MI_CLK = 0;
    logic MI_RESET;
    logic RESET;

    iFrameLinkURx #(512,6,3) RX(FLU_CLK, FLU_RESET);
    iLbusTx                  TX(CMAC_CLK, CMAC_RESET);
    iMi32                    MI(MI_CLK, MI_RESET);

    always #(FLU_CLK_PERIOD/2) FLU_CLK = ~FLU_CLK;
    always #(CMAC_CLK_PERIOD/2) CMAC_CLK = ~CMAC_CLK;
    always #(MI_CLK_PERIOD/2) MI_CLK = ~MI_CLK;

    always @(posedge FLU_CLK) FLU_RESET = RESET;
    always @(posedge CMAC_CLK) CMAC_RESET = RESET;
    always @(posedge MI_CLK) MI_RESET = RESET;

    DUT DUT_U (
        .FLU_CLK    (FLU_CLK),
        .FLU_RESET  (FLU_RESET),
        .CMAC_CLK   (CMAC_CLK),
        .CMAC_RESET (CMAC_RESET),
        .MI_CLK     (MI_CLK),
        .MI_RESET   (MI_RESET),
        .RX         (RX),
        .TX         (TX),
        .MI         (MI)
    );

    TEST TEST_U (
        .RESET   (RESET),
        .RX      (RX),
        .TX      (TX),
        .MI      (MI),
        .MONITOR (TX)
    );

endmodule
