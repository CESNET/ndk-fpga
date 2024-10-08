/*!
 * \file dut.sv
 * \brief Design Under Test
 * \author Daniel Kříž <xkrizd01@vutbr.cz>
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

import test_pkg::*;

module DUT (
    input logic CLK,
    input logic RESET,
    iMvbRx.dut RX0,
    iMvbRx.dut RX1,
    iMvbTx.dut TX
);

    MVB_MERGE_ITEMS #(
        .RX0_ITEMS      (RX0_ITEMS),
        .RX0_ITEM_WIDTH (RX0_ITEM_WIDTH),
        .RX1_ITEMS      (RX1_ITEMS),
        .RX1_ITEM_WIDTH (RX1_ITEM_WIDTH)
    ) VHDL_DUT_U (
        .CLK          (CLK),
        .RESET        (RESET),

        .RX0_DATA     (RX0.DATA),
        .RX0_VLD      (RX0.VLD),
        .RX0_SRC_RDY  (RX0.SRC_RDY),
        .RX0_DST_RDY  (RX0.DST_RDY),

        .RX1_DATA     (RX1.DATA),
        .RX1_VLD      (RX1.VLD),
        .RX1_SRC_RDY  (RX1.SRC_RDY),
        .RX1_DST_RDY  (RX1.DST_RDY),

        .TX_DATA      (TX.DATA),
        .TX_VLD       (TX.VLD),
        .TX_SRC_RDY   (TX.SRC_RDY),
        .TX_DST_RDY   (TX.DST_RDY)
    );

endmodule
