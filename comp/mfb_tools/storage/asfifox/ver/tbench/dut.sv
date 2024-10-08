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
    iMfbRx.dut RX,
    input logic TX_CLK,
    iMfbTx.dut TX
);


    MFB_ASFIFOX #(
        .DEVICE          (DEVICE),
        .MFB_REGIONS     (MFB_REGIONS),
        .MFB_REG_SIZE    (MFB_REG_SIZE),
        .MFB_BLOCK_SIZE  (MFB_BLOCK_SIZE),
        .MFB_ITEM_WIDTH  (MFB_ITEM_WIDTH),
        .FIFO_ITEMS      (FIFO_ITEMS)
    ) VHDL_DUT_U (
        .RX_CLK      (RX_CLK),
        .RX_RESET    (RESET),
        .RX_DATA     (RX.DATA),
        .RX_SOF_POS  (RX.SOF_POS),
        .RX_EOF_POS  (RX.EOF_POS),
        .RX_SOF      (RX.SOF),
        .RX_EOF      (RX.EOF),
        .RX_SRC_RDY  (RX.SRC_RDY),
        .RX_DST_RDY  (RX.DST_RDY),
        .TX_CLK      (TX_CLK),
        .TX_RESET    (RESET),
        .TX_DATA     (TX.DATA),
        .TX_SOF_POS  (TX.SOF_POS),
        .TX_EOF_POS  (TX.EOF_POS),
        .TX_SOF      (TX.SOF),
        .TX_EOF      (TX.EOF),
        .TX_SRC_RDY  (TX.SRC_RDY),
        .TX_DST_RDY  (TX.DST_RDY)
    );

endmodule
