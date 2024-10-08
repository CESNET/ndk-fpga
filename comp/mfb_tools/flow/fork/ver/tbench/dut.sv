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
    iMfbRx.dut RX,
    iMfbTx.dut TX[OUTPUT_PORTS]
);

    localparam SOF_POS_WIDTH = REGIONS*math_pkg::max(1,math_pkg::log2(REGION_SIZE));
    localparam EOF_POS_WIDTH = REGIONS*math_pkg::max(1,math_pkg::log2(REGION_SIZE*BLOCK_SIZE));
    logic [OUTPUT_PORTS*REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 : 0] data;
    logic [OUTPUT_PORTS*REGIONS*META_WIDTH-1 : 0] meta;
    logic [OUTPUT_PORTS*SOF_POS_WIDTH-1 : 0] sof_pos;
    logic [OUTPUT_PORTS*EOF_POS_WIDTH-1 : 0] eof_pos;
    logic [OUTPUT_PORTS*REGIONS-1 : 0] sof, eof;
    logic [OUTPUT_PORTS-1 : 0] src_rdy, dst_rdy;
    genvar i;

    generate for (i=0; i < OUTPUT_PORTS; i++) begin
        assign TX[i].DATA = data[(i+1)*REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH-1 : REGIONS*REGION_SIZE*BLOCK_SIZE*ITEM_WIDTH*i];
        assign TX[i].META = meta[(i+1)*REGIONS*META_WIDTH-1 : REGIONS*META_WIDTH*i];
        assign TX[i].SOF_POS = sof_pos[(i+1)*SOF_POS_WIDTH-1 : SOF_POS_WIDTH*i];
        assign TX[i].EOF_POS = eof_pos[(i+1)*EOF_POS_WIDTH-1 : EOF_POS_WIDTH*i];
        assign TX[i].SOF = sof[(i+1)*REGIONS-1 : REGIONS*i];
        assign TX[i].EOF = eof[(i+1)*REGIONS-1 : REGIONS*i];
        assign TX[i].SRC_RDY = src_rdy[i];
        assign dst_rdy[i] = TX[i].DST_RDY;
    end endgenerate

    MFB_FORK #(
        .OUTPUT_PORTS (OUTPUT_PORTS),
        .REGIONS      (REGIONS),
        .REGION_SIZE  (REGION_SIZE),
        .BLOCK_SIZE   (BLOCK_SIZE),
        .ITEM_WIDTH   (ITEM_WIDTH),
        .META_WIDTH   (META_WIDTH),
        .USE_DST_RDY  (USE_DST_RDY),
        .VERSION      (VERSION)
    ) VHDL_DUT_U (
        .CLK          (CLK),
        .RESET        (RESET),

        .RX_DATA      (RX.DATA),
        .RX_META      (RX.META),
        .RX_SOF_POS   (RX.SOF_POS),
        .RX_EOF_POS   (RX.EOF_POS),
        .RX_SOF       (RX.SOF),
        .RX_EOF       (RX.EOF),
        .RX_SRC_RDY   (RX.SRC_RDY),
        .RX_DST_RDY   (RX.DST_RDY),

        .TX_DATA      (data),
        .TX_META      (meta),
        .TX_SOF_POS   (sof_pos),
        .TX_EOF_POS   (eof_pos),
        .TX_SOF       (sof),
        .TX_EOF       (eof),
        .TX_SRC_RDY   (src_rdy),
        .TX_DST_RDY   (dst_rdy)
    );

endmodule
