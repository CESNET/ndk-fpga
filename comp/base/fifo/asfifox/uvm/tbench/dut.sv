//-- dut.sv: Design under test
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT (
    input logic     RX_CLK,
    input logic     TX_CLK,
    input logic     RX_RST,
    input logic     TX_RST,
    mvb_if.dut_rx   mvb_wr,
    mvb_if.dut_tx   mvb_rd
    );

    logic FIFO_EMPTY;
    logic FIFO_FULL;
    logic FIFO_VLD_AND_SRC_RDY;


    assign mvb_rd.VLD     = ~FIFO_EMPTY;
    assign mvb_rd.SRC_RDY = ~FIFO_EMPTY;
    assign mvb_wr.DST_RDY = ~FIFO_FULL;
    assign FIFO_VLD_AND_SRC_RDY = mvb_wr.SRC_RDY; //& mvb_wr.VLD[0];

    ASFIFOX #(
        .ITEMS       (FIFO_ITEMS),
        .DATA_WIDTH  (ITEM_WIDTH)
    ) VHDL_DUT_U (
        .WR_CLK      (RX_CLK),
        .WR_RST      (RX_RST),
        .WR_DATA     (mvb_wr.DATA),
        .WR_EN       (FIFO_VLD_AND_SRC_RDY),
        .WR_FULL     (FIFO_FULL),
        .WR_AFULL    (),
        .WR_STATUS   (),

        .RD_CLK      (TX_CLK),
        .RD_RST      (TX_RST),
        .RD_DATA     (mvb_rd.DATA),
        .RD_EMPTY    (FIFO_EMPTY),
        .RD_EN       (mvb_rd.DST_RDY),
        .RD_AEMPTY   (),
        .RD_STATUS   ()
    );


endmodule
