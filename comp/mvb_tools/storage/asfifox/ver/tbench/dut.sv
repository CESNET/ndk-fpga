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
    input logic RESET,
    input logic RX_CLK,
    iMvbRx.dut RX,
    input logic TX_CLK,
    iMvbTx.dut TX
);


    MVB_ASFIFOX #(
        .DEVICE         (DEVICE),
        .MVB_ITEMS      (MVB_ITEMS),
        .MVB_ITEM_WIDTH (MVB_ITEM_WIDTH),
        .FIFO_ITEMS     (FIFO_ITEMS)
    ) VHDL_DUT_U (
        .RX_CLK      (RX_CLK),
        .RX_RESET    (RESET),
        .RX_DATA     (RX.DATA),
        .RX_VLD      (RX.VLD),
        .RX_SRC_RDY  (RX.SRC_RDY),
        .RX_DST_RDY  (RX.DST_RDY),
        .TX_CLK      (TX_CLK),
        .TX_RESET    (RESET),
        .TX_DATA     (TX.DATA),
        .TX_VLD      (TX.VLD),
        .TX_SRC_RDY  (TX.SRC_RDY),
        .TX_DST_RDY  (TX.DST_RDY)
    );

endmodule
