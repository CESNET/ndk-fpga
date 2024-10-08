// dut.sv
// Copyright (C) 2019 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;

module DUT (
    input logic CLK,
    input logic RESET,
    iMiiRx.dut MII,
    iMfbTx.dut MFB
);

    UMII_DEC #(
        .MII_DW      (MII_DATA_WIDTH),
        .REGIONS     (REGIONS),
        .REGION_SIZE (REGION_SIZE),
        .BLOCK_SIZE  (BLOCK_SIZE),
        .ITEM_WIDTH  (ITEM_WIDTH)
    ) VHDL_DUT_U (
        .CLK            (CLK),
        .RESET          (RESET),

        .MII_RXD        (MII.RXD),
        .MII_RXC        (MII.RXC),
        .MII_VLD        (1'b1),

        .TX_DATA        (MFB.DATA),
        .TX_SOF_POS     (MFB.SOF_POS),
        .TX_EOF_POS     (MFB.EOF_POS),
        .TX_SOF         (MFB.SOF),
        .TX_EOF         (MFB.EOF),
        .TX_ERR         (),
        .TX_SRC_RDY     (MFB.SRC_RDY),

        .LINK_UP        (),
        .INCOMING_FRAME ()
    );

endmodule
