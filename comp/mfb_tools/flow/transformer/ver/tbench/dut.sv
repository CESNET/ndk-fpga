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


    MFB_TRANSFORMER #(
        .RX_REGIONS  (RX_REGIONS),
        .TX_REGIONS  (TX_REGIONS),
        .REGION_SIZE (REGION_SIZE),
        .BLOCK_SIZE  (BLOCK_SIZE),
        .ITEM_WIDTH  (ITEM_WIDTH)
    ) VHDL_DUT_U (
        .CLK         (CLK),
        .RESET       (RESET),
        .RX_DATA     (RX.DATA),
        .RX_SOP_POS  (RX.SOF_POS),
        .RX_EOP_POS  (RX.EOF_POS),
        .RX_SOP      (RX.SOF),
        .RX_EOP      (RX.EOF),
        .RX_SRC_RDY  (RX.SRC_RDY),
        .RX_DST_RDY  (RX.DST_RDY),
        .TX_DATA     (TX.DATA),
        .TX_SOP_POS  (TX.SOF_POS),
        .TX_EOP_POS  (TX.EOF_POS),
        .TX_SOP      (TX.SOF),
        .TX_EOP      (TX.EOF),
        .TX_SRC_RDY  (TX.SRC_RDY),
        .TX_DST_RDY  (TX.DST_RDY)
    );

endmodule

