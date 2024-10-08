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
    input logic RX_CLK,
    input logic TX_CLK,
    input logic RX_RST,
    input logic TX_RST,
    iMvbRx.dut RX,
    iMvbTx.dut TX
);

logic FIFO_EMPTY;
logic FIFO_FULL;

    ASFIFOX #(
        .ITEMS       (FIFO_ITEMS),
        .DATA_WIDTH  (DATA_WIDTH)
    ) VHDL_DUT_U (
        .WR_CLK      (RX_CLK),
        .WR_RST      (RX_RST),
        .WR_DATA     (RX.DATA),
        .WR_EN       (RX.SRC_RDY),
        .WR_FULL     (FIFO_FULL),

        .RD_CLK      (TX_CLK),
        .RD_RST      (TX_RST),
        .RD_DATA     (TX.DATA),
        .RD_EMPTY    (FIFO_EMPTY),
        .RD_EN       (TX.DST_RDY)
    );

assign TX.VLD = 1;
assign TX.SRC_RDY = !FIFO_EMPTY;
assign RX.DST_RDY = !FIFO_FULL;
endmodule
