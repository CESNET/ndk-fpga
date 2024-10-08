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

module DUT (
    input logic CLK,
    input logic RESET,
    iMfbRx.dut RX0,
    iMfbRx.dut RX1,
    iMfbTx.dut TX
);

    MFB_MERGER_SIMPLE #(
        .REGIONS     (REGIONS),
        .REGION_SIZE (REGION_SIZE),
        .BLOCK_SIZE  (BLOCK_SIZE),
        .ITEM_WIDTH  (ITEM_WIDTH)
    ) VHDL_DUT_U (
        .CLK         (CLK),
        .RST         (RESET),

        .RX_MFB0_DATA    (RX0.DATA),
        .RX_MFB0_SOF_POS (RX0.SOF_POS),
        .RX_MFB0_EOF_POS (RX0.EOF_POS),
        .RX_MFB0_SOF     (RX0.SOF),
        .RX_MFB0_EOF     (RX0.EOF),
        .RX_MFB0_SRC_RDY (RX0.SRC_RDY),
        .RX_MFB0_DST_RDY (RX0.DST_RDY),

        .RX_MFB1_DATA    (RX1.DATA),
        .RX_MFB1_SOF_POS (RX1.SOF_POS),
        .RX_MFB1_EOF_POS (RX1.EOF_POS),
        .RX_MFB1_SOF     (RX1.SOF),
        .RX_MFB1_EOF     (RX1.EOF),
        .RX_MFB1_SRC_RDY (RX1.SRC_RDY),
        .RX_MFB1_DST_RDY (RX1.DST_RDY),

        .TX_MFB_DATA     (TX.DATA),
        .TX_MFB_SOF_POS  (TX.SOF_POS),
        .TX_MFB_EOF_POS  (TX.EOF_POS),
        .TX_MFB_SOF      (TX.SOF),
        .TX_MFB_EOF      (TX.EOF),
        .TX_MFB_SRC_RDY  (TX.SRC_RDY),
        .TX_MFB_DST_RDY  (TX.DST_RDY)
    );

endmodule
