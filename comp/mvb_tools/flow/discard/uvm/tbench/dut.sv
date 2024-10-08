//-- dut.sv: Design under test
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author:   Jakub Cabal <cabal@cesnet.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT (
    input logic     CLK,
    input logic     RST,
    mvb_if.dut_rx   mvb_wr,
    mvb_if.dut_tx   mvb_rd
    );

    DUT_WRAPPER #(
        .ITEMS       (ITEMS),
        .ITEM_WIDTH  (ITEM_WIDTH)
    ) VHDL_DUT_U (
        .CLK        (CLK),
        .RESET      (RST),

        .RX_DATA    (mvb_wr.DATA),
        .RX_VLD     (mvb_wr.VLD),
        .RX_SRC_RDY (mvb_wr.SRC_RDY),
        .RX_DST_RDY (mvb_wr.DST_RDY),

        .TX_DATA    (mvb_rd.DATA),
        .TX_VLD     (mvb_rd.VLD),
        .TX_SRC_RDY (mvb_rd.SRC_RDY),
        .TX_DST_RDY (mvb_rd.DST_RDY)
    );

endmodule
