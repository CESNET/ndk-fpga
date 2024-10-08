// dut.sv: Design under test
// Copyright (C) 2020 CESNET
// Author: Tomas Hak <xhakto01@stud.fit.vutbr.cz>
// SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;

module DUT (
    input logic CLK,
    input logic RESET,
    iMfbRx.dut RX,
    iMfbTx.dut TX
);

    MFB_ITEM_RECONFIGURATOR #(
        .REGIONS        (REGIONS),
        .REGION_SIZE    (REGION_SIZE),
        .RX_BLOCK_SIZE  (RX_BLOCK_SIZE),
        .TX_BLOCK_SIZE  (TX_BLOCK_SIZE),
        .RX_ITEM_WIDTH  (RX_ITEM_WIDTH),
        .META_WIDTH     (META_WIDTH),
        .DEVICE         (DEVICE)
    ) VHDL_DUT_U (
        .CLK         (CLK),
        .RESET       (RESET),
        .RX_DATA     (RX.DATA),
        .RX_META     (RX.META),
        .RX_SOF      (RX.SOF),
        .RX_EOF      (RX.EOF),
        .RX_SOF_POS  (RX.SOF_POS),
        .RX_EOF_POS  (RX.EOF_POS),
        .RX_SRC_RDY  (RX.SRC_RDY),
        .RX_DST_RDY  (RX.DST_RDY),
        .TX_DATA     (TX.DATA),
        .TX_META     (TX.META),
        .TX_SOF      (TX.SOF),
        .TX_EOF      (TX.EOF),
        .TX_SOF_POS  (TX.SOF_POS),
        .TX_EOF_POS  (TX.EOF_POS),
        .TX_SRC_RDY  (TX.SRC_RDY),
        .TX_DST_RDY  (TX.DST_RDY)
    );

endmodule

