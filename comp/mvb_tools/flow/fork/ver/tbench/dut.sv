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
    iMvbRx.dut RX,
    iMvbTx.dut TX[OUTPUT_PORTS]
);

    logic [OUTPUT_PORTS*ITEMS*ITEM_WIDTH-1 : 0] data;
    logic [OUTPUT_PORTS*ITEMS-1 : 0] vld;
    logic [OUTPUT_PORTS-1 : 0] src_rdy, dst_rdy;
    genvar i;

    generate for (i=0; i < OUTPUT_PORTS; i++) begin
        assign TX[i].DATA    = data[(i+1)*ITEMS*ITEM_WIDTH-1 : ITEMS*ITEM_WIDTH*i];
        assign TX[i].VLD     = vld[(i+1)*ITEMS-1 : ITEMS*i];
        assign TX[i].SRC_RDY = src_rdy[i];
        assign dst_rdy[i]    = TX[i].DST_RDY;
    end endgenerate

    MVB_FORK #(
        .OUTPUT_PORTS (OUTPUT_PORTS),
        .ITEMS        (ITEMS),
        .ITEM_WIDTH   (ITEM_WIDTH),
        .USE_DST_RDY  (USE_DST_RDY),
        .VERSION      (VERSION)
    ) VHDL_DUT_U (
        .CLK          (CLK),
        .RESET        (RESET),

        .RX_DATA      (RX.DATA),
        .RX_VLD       (RX.VLD),
        .RX_SRC_RDY   (RX.SRC_RDY),
        .RX_DST_RDY   (RX.DST_RDY),

        .TX_DATA      (data),
        .TX_VLD       (vld),
        .TX_SRC_RDY   (src_rdy),
        .TX_DST_RDY   (dst_rdy)
    );

endmodule
