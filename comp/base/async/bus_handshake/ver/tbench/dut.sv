// dut.sv
// Copyright (C) 2020 CESNET z. s. p. o.
// Author(s): Jakub Cabal <cabal@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;

module DUT (
    input logic RX_CLK,
    input logic TX_CLK,
    input logic RX_RST,
    input logic TX_RST,
    iMvbRx.dut RX,
    iMvbTx.dut TX
);

    ASYNC_BUS_HANDSHAKE #(
        .DATA_WIDTH  (DATA_WIDTH),
        .DATA_RESET  (0)
    ) VHDL_DUT_U (
        .ACLK     (RX_CLK),
        .ARST     (RX_RST),
        .ADATAIN  (RX.DATA),
        .ASEND    (RX.SRC_RDY),
        .AREADY   (RX.DST_RDY),
        .BCLK     (TX_CLK),
        .BRST     (TX_RST),
        .BDATAOUT (TX.DATA),
        .BLOAD    (TX.DST_RDY),
        .BVALID   (TX.SRC_RDY)
    );

    assign TX.VLD = 1;

endmodule
