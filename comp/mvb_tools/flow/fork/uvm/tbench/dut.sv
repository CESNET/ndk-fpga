// dut.sv: Design under test
// MVB_FORK UVM verification
// Copyright (C) 2026 CESNET z. s. p. o.
// Author(s): Alena Drlickova <drlickova@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import test::*;

module dut (
    input logic             CLK,
    input logic             RST,
    mvb_if.dut_rx           mvb_wr,
    mvb_if.dut_tx           mvb_rd[OUTPUT_PORTS]
    );

    logic [OUTPUT_PORTS*ITEMS*ITEM_WIDTH-1 : 0] data;
    logic [OUTPUT_PORTS*ITEMS-1 : 0]           vld;
    logic [OUTPUT_PORTS-1 : 0]                 src_rdy;
    logic [OUTPUT_PORTS-1 : 0]                 dst_rdy;
    genvar                                     i;

    generate for (i = 0; i < OUTPUT_PORTS; i++) begin : gen_tx
        assign mvb_rd[i].DATA    = data[(i+1)*ITEMS*ITEM_WIDTH-1 : ITEMS*ITEM_WIDTH*i];
        assign mvb_rd[i].VLD     = vld[(i+1)*ITEMS-1 : ITEMS*i];
        assign mvb_rd[i].SRC_RDY = src_rdy[i];
        assign dst_rdy[i]        = mvb_rd[i].DST_RDY;
    end endgenerate

    MVB_FORK #(
        .OUTPUT_PORTS (OUTPUT_PORTS),
        .ITEMS        (ITEMS),
        .ITEM_WIDTH   (ITEM_WIDTH),
        .USE_DST_RDY  (USE_DST_RDY),
        .VERSION      (VERSION)
    ) VHDL_DUT_U (
        .CLK          (CLK),
        .RESET        (RST),

        .RX_DATA      (mvb_wr.DATA),
        .RX_VLD       (mvb_wr.VLD),
        .RX_SRC_RDY   (mvb_wr.SRC_RDY),
        .RX_DST_RDY   (mvb_wr.DST_RDY),

        .TX_DATA      (data),
        .TX_VLD       (vld),
        .TX_SRC_RDY   (src_rdy),
        .TX_DST_RDY   (dst_rdy)
    );

endmodule
