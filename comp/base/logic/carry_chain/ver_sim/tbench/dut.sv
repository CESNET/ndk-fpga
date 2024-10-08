/*!
 * \file dut.sv
 * \brief Design Under Test
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

import test_pkg::*;



module DUT (
    input logic CLK,
    input logic RESET,
    iWordLinkRx.dut RX
);


    CARRY_CHAIN #(
        .CARRY_WIDTH    (CARRY_WIDTH),
        .DEVICE         ("7SERIES")
    ) VHDL_DUT_U (
        .CI (RX.DATA[2*CARRY_WIDTH]),
        .DI (RX.DATA[0 +: CARRY_WIDTH]),
        .S  (RX.DATA[CARRY_WIDTH +: CARRY_WIDTH]),
        .CO (),
        .DO ()
    );

endmodule
