// file dut.sv: Design Under Test
// Copyright (C) 2022 CESNET z. s. p. o.
// Author(s): Daniel Kondys <xkondy00@vutbr.cz>
//
// SPDX-License-Identifier: BSD-3-Clause


import test_pkg::*;

module DUT (
    input logic CLK,
    input logic RESET,
    iMfbRx.dut RX,
    iMfbTx.dut TX
);

    //RX.SOF_POS RX SOF is unconnected
    ETH_AVST_ADAPTER_SHAKEDOWN #(
        .DATA_WIDTH     (DATA_WIDTH),
        .TX_REGION_SIZE (TX_REGION_SIZE)
    ) VHDL_DUT_U (
        .CLK               (CLK),
        .RESET             (RESET),
        .IN_MFB_DATA       (RX.DATA),
        .IN_MFB_SOF        (RX.SOF),
        .IN_MFB_EOF        (RX.EOF),
        .IN_MFB_EOF_POS    (RX.EOF_POS),
        .IN_MFB_UNDERSIZED (RX.META[0]),
        .IN_MFB_SRC_RDY    (RX.SRC_RDY),
        .OUT_MFB_DATA      (TX.DATA),
        .OUT_MFB_SOF       (TX.SOF),
        .OUT_MFB_SOF_POS   (TX.SOF_POS),
        .OUT_MFB_EOF       (TX.EOF),
        .OUT_MFB_EOF_POS   (TX.EOF_POS),
        .OUT_MFB_SRC_RDY   (TX.SRC_RDY)
    );

    assign RX.DST_RDY = 1'b1;
    //assign RX.META[0] = 1'b0;

endmodule
