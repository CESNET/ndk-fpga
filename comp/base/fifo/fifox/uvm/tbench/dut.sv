// dut.sv: Design under test
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT (
    input logic CLK,
    input logic RST,
    mvb_if.dut_rx mvb_rx,
    mvb_if.dut_tx mvb_tx,
    mvb_if.dut_tx mvb_status
);

    bind FIFOX : VHDL_DUT_U probe_inf #(2) probe_status((RESET === 1'b0), { wr_en, rd_en }, CLK);

    logic wr;
    logic full;

    logic empty;

    logic [STATUS_WIDTH-1 : 0] status;
    logic aempty;
    logic afull;

    FIFOX #(

        .DATA_WIDTH          (DATA_WIDTH         ),
        .ITEMS               (ITEMS              ),
        .RAM_TYPE            (RAM_TYPE           ),
        .DEVICE              (DEVICE             ),
        .ALMOST_FULL_OFFSET  (ALMOST_FULL_OFFSET ),
        .ALMOST_EMPTY_OFFSET (ALMOST_EMPTY_OFFSET),
        .FAKE_FIFO           (FAKE_FIFO          )

    ) VHDL_DUT_U (

        .CLK   (CLK),
        .RESET (RST),

        .DI     (mvb_rx.DATA),
        .WR     (wr         ),
        .FULL   (full       ),
        .AFULL  (afull      ),
        .STATUS (status     ),

        .DO     (mvb_tx.DATA   ),
        .RD     (mvb_tx.DST_RDY),
        .EMPTY  (empty         ),
        .AEMPTY (aempty        )

    );

    assign wr = mvb_rx.VLD & mvb_rx.SRC_RDY;
    assign mvb_rx.DST_RDY = ~full;

    assign mvb_tx.VLD = 1;
    assign mvb_tx.SRC_RDY = ~empty;

    assign mvb_status.DATA = { status, afull, aempty };
    assign mvb_status.VLD = (RST === 1'b0);
    assign mvb_status.SRC_RDY = 1;
    assign mvb_status.DST_RDY = 1;

endmodule
