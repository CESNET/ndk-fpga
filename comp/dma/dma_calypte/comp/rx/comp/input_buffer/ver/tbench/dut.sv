// dut.sv: Design Under Test
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Vladislav Valek <valekv@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-CLause

import test_pkg::*;

module DUT (
    input logic CLK,
    input logic RESET,
    iMfbRx.dut RX,
    iMfbTx.dut TX
);

    RX_DMA_CALYPTE_INPUT_BUFFER #(
        .REGION_SIZE (REGION_SIZE),
        .BLOCK_SIZE  (BLOCK_SIZE),
        .ITEM_WIDTH  (ITEM_WIDTH)
    ) VHDL_DUT_U (
        .CLK   (CLK),
        .RST   (RESET),

        .RX_MFB_DATA    (RX.DATA),
        .RX_MFB_SOF_POS (RX.SOF_POS),
        .RX_MFB_EOF_POS (RX.EOF_POS),
        .RX_MFB_SOF     (RX.SOF),
        .RX_MFB_EOF     (RX.EOF),
        .RX_MFB_SRC_RDY (RX.SRC_RDY),
        .RX_MFB_DST_RDY (RX.DST_RDY),

        .TX_MFB_DATA    (TX.DATA),
        .TX_MFB_SOF_POS (TX.SOF_POS),
        .TX_MFB_EOF_POS (TX.EOF_POS),
        .TX_MFB_SOF     (TX.SOF),
        .TX_MFB_EOF     (TX.EOF),
        .TX_MFB_SRC_RDY (TX.SRC_RDY),
        .TX_MFB_DST_RDY (TX.DST_RDY)
    );

endmodule
