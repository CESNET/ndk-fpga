// dut.sv
// Copyright (C) 2019 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;

module DUT (
    input logic CLK,
    input logic RESET,
    iMiiTx.dut MII,
    iMfbRx.dut MFB
);

    UMII_ENC #(
        .MII_DW      (MII_DATA_WIDTH),
        .REGIONS     (REGIONS),
        .REGION_SIZE (REGION_SIZE),
        .BLOCK_SIZE  (BLOCK_SIZE),
        .ITEM_WIDTH  (ITEM_WIDTH)
    ) VHDL_DUT_U (
        .CLK        (CLK),
        .RESET      (RESET),

        .RX_DATA    (MFB.DATA),
        .RX_SOF_POS (MFB.SOF_POS),
        .RX_EOF_POS (MFB.EOF_POS),
        .RX_SOF     (MFB.SOF),
        .RX_EOF     (MFB.EOF),
        .RX_SRC_RDY (MFB.SRC_RDY),
        .RX_DST_RDY (MFB.DST_RDY),

        .MII_TXD    (MII.TXD),
        .MII_TXC    (MII.TXC),
        .MII_VLD    (),
        .MII_RDY    (1'b1)
    );

endmodule
