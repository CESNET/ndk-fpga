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
    iMfbRx.dut RX,
    iMfbTx.dut TX0,
    iMfbTx.dut TX1
);

    MFB_DUPLICATION #(
        .REGIONS     (REGIONS),
        .REGION_SIZE (REGION_SIZE),
        .BLOCK_SIZE  (BLOCK_SIZE),
        .ITEM_WIDTH  (ITEM_WIDTH)
    ) VHDL_DUT_U (
        .CLK         (CLK),
        .RST         (RESET),
        .RX_DATA     (RX.DATA),
        .RX_SOF_POS  (RX.SOF_POS),
        .RX_EOF_POS  (RX.EOF_POS),
        .RX_SOF      (RX.SOF),
        .RX_EOF      (RX.EOF),
        .RX_SRC_RDY  (RX.SRC_RDY),
        .RX_DST_RDY  (RX.DST_RDY),
        .TX0_DATA     (TX0.DATA),
        .TX0_SOF_POS  (TX0.SOF_POS),
        .TX0_EOF_POS  (TX0.EOF_POS),
        .TX0_SOF      (TX0.SOF),
        .TX0_EOF      (TX0.EOF),
        .TX0_SRC_RDY  (TX0.SRC_RDY),
        .TX0_DST_RDY  (TX0.DST_RDY),
        .TX1_DATA     (TX1.DATA),
        .TX1_SOF_POS  (TX1.SOF_POS),
        .TX1_EOF_POS  (TX1.EOF_POS),
        .TX1_SOF      (TX1.SOF),
        .TX1_EOF      (TX1.EOF),
        .TX1_SRC_RDY  (TX1.SRC_RDY),
        .TX1_DST_RDY  (TX1.DST_RDY)
    );

endmodule
