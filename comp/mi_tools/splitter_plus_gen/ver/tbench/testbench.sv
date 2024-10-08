/*!
 * \file testbench.sv
 * \brief Testbench
 * \author Daniel Kondys <xkondy00@vutbr.cz>
 * \date 2020
 */
 /*
 * Copyright (C) 2020 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import test_pkg::*;

module testbench;

    logic CLK = 0;
    logic RESET;
    iMi   #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) MI_RX(CLK, RESET);
    iMi   #(DATA_WIDTH, ADDR_WIDTH, META_WIDTH) MI_TX[PORTS](CLK, RESET);

    always #(CLK_PERIOD/2) CLK = ~CLK;

    DUT VHDL_DUT_U (
        .CLK          (CLK),
        .RESET        (RESET),
        .RX           (MI_RX),
        .TX           (MI_TX)
    );

    TEST TEST_U (
        .CLK            (CLK),
        .RESET          (RESET),
        .MI_MASTER      (MI_RX),
        .MI_SLAVE       (MI_TX)
    );

endmodule
