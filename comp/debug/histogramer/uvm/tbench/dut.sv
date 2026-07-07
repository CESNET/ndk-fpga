//-- dut.sv: Design under test
//-- Copyright (C) 2022 CESNET z. s. p. o.
//-- Author: Lukas Nevrkla <xnevrk03@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause

import test::*;

module dut #(
    int unsigned    INPUT_WIDTH,
    int unsigned    BOX_WIDTH,
    int unsigned    BOX_CNT,
    logic           READ_PRIOR,
    logic           CLEAR_BY_READ,
    logic           CLEAR_BY_RST,
    string          DEVICE,
    int unsigned    REQ_WIDTH,
    int unsigned    RESP_WIDTH
)(
    input logic     CLK,
    input logic     RST,
    mvb_if.dut_rx   mvb_req,
    mvb_if.dut_tx   mvb_resp
);

    logic                           RST_DONE;
    logic                           INPUT_VLD;
    logic [INPUT_WIDTH - 1 : 0]     INPUT;
    logic                           READ_REQ;
    logic [$clog2(BOX_CNT) - 1 : 0] READ_ADDR;
    logic                           READ_BOX_VLD;
    logic [BOX_WIDTH - 1 : 0]       READ_BOX;

    logic                           req;
    logic                           read_req;

    assign mvb_req.DST_RDY              = RST_DONE;
    assign req                          = mvb_req.SRC_RDY & mvb_req.VLD;
    assign {read_req, INPUT, READ_ADDR} = mvb_req.DATA;

    assign INPUT_VLD                    = req & ! read_req;
    assign READ_REQ                     = req &   read_req;

    assign mvb_resp.DST_RDY  = 2'b1;
    assign mvb_resp.SRC_RDY  = READ_BOX_VLD;
    assign mvb_resp.VLD      = READ_BOX_VLD;
    assign mvb_resp.DATA     = READ_BOX;

    HISTOGRAMER #(
        .INPUT_WIDTH        (INPUT_WIDTH  ),
        .BOX_WIDTH          (BOX_WIDTH    ),
        .BOX_CNT            (BOX_CNT      ),
        .READ_PRIOR         (READ_PRIOR   ),
        .CLEAR_BY_READ      (CLEAR_BY_READ),
        .CLEAR_BY_RST       (CLEAR_BY_RST )
    ) VHDL_DUT_U (
        .CLK                (CLK         ),
        .RST                (RST         ),
        .RST_DONE           (RST_DONE    ),

        .INPUT_VLD          (INPUT_VLD   ),
        .INPUT              (INPUT       ),

        .READ_REQ           (READ_REQ    ),
        .READ_ADDR          (READ_ADDR   ),

        .READ_BOX_VLD       (READ_BOX_VLD),
        .READ_BOX           (READ_BOX    )
    );
endmodule
