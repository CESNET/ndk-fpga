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
    iMvbTx.dut TX[ITEMS]
);


    logic [ITEMS*ITEM_WIDTH-1 : 0] data;
    logic [ITEMS-1 : 0] src_rdy, dst_rdy;
    genvar i;

    generate for (i=0; i < ITEMS; i++) begin
        assign TX[i].DATA = data[(i+1)*ITEM_WIDTH-1 : ITEM_WIDTH*i];
        assign TX[i].VLD = src_rdy[i];
        assign TX[i].SRC_RDY = src_rdy[i];
        assign dst_rdy[i] = TX[i].DST_RDY;
    end endgenerate

    MVB_SPLIT #(
        .ITEMS       (ITEMS),
        .ITEM_WIDTH  (ITEM_WIDTH),
        .USE_DST_RDY (USE_DST_RDY)
    ) VHDL_DUT_U (
        .CLK         (CLK),
        .RESET       (RESET),
        .RX_DATA     (RX.DATA),
        .RX_VLD      (RX.VLD),
        .RX_SRC_RDY  (RX.SRC_RDY),
        .RX_DST_RDY  (RX.DST_RDY),
        .TX_DATA     (data),
        .TX_SRC_RDY  (src_rdy),
        .TX_DST_RDY  (dst_rdy)
    );

endmodule
