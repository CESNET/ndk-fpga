/*!
 * \file dut.sv
 * \brief Design Under Test
 * \author Jakub Cabal <xcabal05@stud.feec.vutbr.cz>
 * \date 2017
 */
 /*
 * Copyright (C) 2017 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import test_pkg::*;
import math_pkg::*;

module DUT (
    input logic CLK,
    input logic RESET,
    iMfbRx.dut RX_MFB[MERGER_INPUTS],
    iMfbTx.dut TX_MFB
);

    localparam SOF_WIDTH = math_pkg::max(1,$clog2(MFB_REGION_SIZE));
    localparam EOF_WIDTH = math_pkg::max(1,$clog2(MFB_REGION_SIZE*MFB_BLOCK_SIZE));

    // Packed 2D wires used to collect the per-input MFB signals into the shape
    // expected by the slv_array_t ports of MFB_MERGER_SIMPLE_GEN.
    logic [MERGER_INPUTS-1:0][MFB_REGIONS*MFB_REGION_SIZE*MFB_BLOCK_SIZE*MFB_ITEM_WIDTH-1:0] rx_mfb_data;
    logic [MERGER_INPUTS-1:0][MFB_REGIONS*MFB_META_WIDTH-1:0] rx_mfb_meta;
    logic [MERGER_INPUTS-1:0][MFB_REGIONS-1:0] rx_mfb_sof;
    logic [MERGER_INPUTS-1:0][MFB_REGIONS-1:0] rx_mfb_eof;
    logic [MERGER_INPUTS-1:0][MFB_REGIONS*SOF_WIDTH-1:0] rx_mfb_sof_pos;
    logic [MERGER_INPUTS-1:0][MFB_REGIONS*EOF_WIDTH-1:0] rx_mfb_eof_pos;
    logic [MERGER_INPUTS-1:0] rx_mfb_src_rdy;
    logic [MERGER_INPUTS-1:0] rx_mfb_dst_rdy;

    generate
        for (genvar i = 0; i < MERGER_INPUTS; i++) begin
            assign rx_mfb_data   [i] = RX_MFB[i].DATA   ;
            assign rx_mfb_meta   [i] = RX_MFB[i].META   ;
            assign rx_mfb_sof    [i] = RX_MFB[i].SOF    ;
            assign rx_mfb_eof    [i] = RX_MFB[i].EOF    ;
            assign rx_mfb_sof_pos[i] = RX_MFB[i].SOF_POS;
            assign rx_mfb_eof_pos[i] = RX_MFB[i].EOF_POS;
            assign rx_mfb_src_rdy[i] = RX_MFB[i].SRC_RDY;
            assign RX_MFB[i].DST_RDY  = rx_mfb_dst_rdy[i];
        end
    endgenerate

    MFB_MERGER_SIMPLE_GEN #(
        .MERGER_INPUTS   (MERGER_INPUTS  ),
        .MFB_REGIONS     (MFB_REGIONS    ),
        .MFB_REGION_SIZE (MFB_REGION_SIZE),
        .MFB_BLOCK_SIZE  (MFB_BLOCK_SIZE ),
        .MFB_ITEM_WIDTH  (MFB_ITEM_WIDTH ),
        .MFB_META_WIDTH  (MFB_META_WIDTH ),
        .CNT_MAX         (CNT_MAX        )
        // MASKING_EN is intentionally left at its entity default (TRUE).
    ) VHDL_DUT_U (
        .CLK             (CLK            ),
        .RST             (RESET          ),

        .RX_MFB_DATA     (rx_mfb_data    ),
        .RX_MFB_META     (rx_mfb_meta    ),
        .RX_MFB_SOF      (rx_mfb_sof     ),
        .RX_MFB_EOF      (rx_mfb_eof     ),
        .RX_MFB_SOF_POS  (rx_mfb_sof_pos ),
        .RX_MFB_EOF_POS  (rx_mfb_eof_pos ),
        .RX_MFB_SRC_RDY  (rx_mfb_src_rdy ),
        .RX_MFB_DST_RDY  (rx_mfb_dst_rdy ),

        .TX_MFB_DATA     (TX_MFB.DATA    ),
        .TX_MFB_META     (TX_MFB.META    ),
        .TX_MFB_SOF      (TX_MFB.SOF     ),
        .TX_MFB_EOF      (TX_MFB.EOF     ),
        .TX_MFB_SOF_POS  (TX_MFB.SOF_POS ),
        .TX_MFB_EOF_POS  (TX_MFB.EOF_POS ),
        .TX_MFB_SRC_RDY  (TX_MFB.SRC_RDY ),
        .TX_MFB_DST_RDY  (TX_MFB.DST_RDY)
    );

endmodule
