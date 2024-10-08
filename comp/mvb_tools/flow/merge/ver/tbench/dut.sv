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
    iMvbRx.dut RX[ITEMS],
    iMvbTx.dut TX
);

    logic [ITEMS*ITEM_WIDTH-1 : 0] data;
    logic [ITEMS-1 : 0] src_rdy, dst_rdy;
    genvar i;

    generate for(i=0; i < ITEMS; i++) begin
        assign data[(i+1)*ITEM_WIDTH-1 : ITEM_WIDTH*i] = RX[i].DATA;
        assign src_rdy[i] = RX[i].SRC_RDY;
        assign RX[i].DST_RDY = dst_rdy[i];
    end endgenerate

    MVB_MERGE #(
        .ITEMS       (ITEMS),
        .ITEM_WIDTH  (ITEM_WIDTH),
        .USE_DST_RDY (USE_DST_RDY)
    ) VHDL_DUT_U (
        .CLK         (CLK),
        .RESET       (RESET),
        .RX_DATA     (data),
        .RX_SRC_RDY  (src_rdy),
        .RX_DST_RDY  (dst_rdy),
        .TX_DATA     (TX.DATA),
        .TX_VLD      (TX.VLD),
        .TX_SRC_RDY  (TX.SRC_RDY),
        .TX_DST_RDY  (TX.DST_RDY)
    );

endmodule
