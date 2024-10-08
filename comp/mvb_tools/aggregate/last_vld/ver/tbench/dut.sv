/*!
 * \file dut.sv
 * \brief Design Under Test
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET z. s. p. o.
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
    iMvbRx.dut RX,
    iMvbTx.dut TX
);


    MVB_AGGREGATE_LAST_VLD #(
        .ITEMS       (ITEMS),
        .ITEM_WIDTH  (ITEM_WIDTH),
        .IMPLEMENTATION (IMPLEMENTATION),
        .INTERNAL_REG   (1)
    ) VHDL_DUT_U (
        .CLK         (CLK),
        .RESET       (RESET),
        .RX_DATA     (RX.DATA),
        .RX_VLD      (RX.VLD),
        .RX_SRC_RDY  (RX.SRC_RDY),
        .RX_DST_RDY  (RX.DST_RDY),
        .TX_DATA     (TX.DATA),
        .TX_VLD      (TX.VLD),
        .TX_SRC_RDY  (TX.SRC_RDY),
        .TX_DST_RDY  (TX.DST_RDY)
    );

endmodule
