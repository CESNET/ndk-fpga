/*!
 * \file dut.sv
 * \brief Design Under Test
 * \author Daniel Kondys <xkondy00@vutbr.cz>
 * \date 2019
 */
 /*
 * Copyright (C) 2019 CESNET z. s. p. o.
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

    MFB_SPLITTER_SIMPLE #(
        .REGIONS     (REGIONS),
        .REGION_SIZE (REGION_SIZE),
        .BLOCK_SIZE  (BLOCK_SIZE),
        .ITEM_WIDTH  (ITEM_WIDTH)
    ) VHDL_DUT_U (
        .CLK             (CLK),
        .RST             (RESET),
        .RX_MFB_SEL      (RX.META),
        .RX_MFB_DATA     (RX.DATA),
        .RX_MFB_META     (),
        .RX_MFB_SOF_POS  (RX.SOF_POS),
        .RX_MFB_EOF_POS  (RX.EOF_POS),
        .RX_MFB_SOF      (RX.SOF),
        .RX_MFB_EOF      (RX.EOF),
        .RX_MFB_SRC_RDY  (RX.SRC_RDY),
        .RX_MFB_DST_RDY  (RX.DST_RDY),
        .TX0_MFB_DATA    (TX0.DATA),
        .TX0_MFB_META    (),
        .TX0_MFB_SOF_POS (TX0.SOF_POS),
        .TX0_MFB_EOF_POS (TX0.EOF_POS),
        .TX0_MFB_SOF     (TX0.SOF),
        .TX0_MFB_EOF     (TX0.EOF),
        .TX0_MFB_SRC_RDY (TX0.SRC_RDY),
        .TX0_MFB_DST_RDY (TX0.DST_RDY),
        .TX1_MFB_DATA    (TX1.DATA),
        .TX1_MFB_META    (),
        .TX1_MFB_SOF_POS (TX1.SOF_POS),
        .TX1_MFB_EOF_POS (TX1.EOF_POS),
        .TX1_MFB_SOF     (TX1.SOF),
        .TX1_MFB_EOF     (TX1.EOF),
        .TX1_MFB_SRC_RDY (TX1.SRC_RDY),
        .TX1_MFB_DST_RDY (TX1.DST_RDY)
    );

endmodule
