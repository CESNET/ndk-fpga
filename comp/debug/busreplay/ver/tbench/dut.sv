/*!
 * \file dut.sv
 * \brief Design Under Test
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2016
 */
 /*
 * Copyright (C) 2016 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import test_pkg::*;



module DUT (
    input logic CLK,
    input logic RESET,
    iFrameLinkURx.dut RX,
    iFrameLinkUTx.dut TX,
    iMi32.dut         MI_DUMP,
    iMi32.dut         MI_REPLAY
);


    logic [TOTAL_WIDTH-1 : 0] in_data, out_data;
    logic out_vld;


    assign RX.DST_RDY = 1;
    assign in_data[DATA_WIDTH-1 : 0] = RX.DATA;
    assign in_data[DATA_WIDTH+SOP_POS_WIDTH-1 : DATA_WIDTH] = RX.SOP_POS;
    assign in_data[DATA_WIDTH+SOP_POS_WIDTH+EOP_POS_WIDTH-1 : DATA_WIDTH+SOP_POS_WIDTH] = RX.EOP_POS;
    assign in_data[DATA_WIDTH+SOP_POS_WIDTH+EOP_POS_WIDTH] = RX.SOP;
    assign in_data[DATA_WIDTH+SOP_POS_WIDTH+EOP_POS_WIDTH+1] = RX.EOP;
    assign in_data[DATA_WIDTH+SOP_POS_WIDTH+EOP_POS_WIDTH+2] = RX.SRC_RDY;
    assign in_data[DATA_WIDTH+SOP_POS_WIDTH+EOP_POS_WIDTH+3] = 1;
    assign TX.DATA = out_data[DATA_WIDTH-1 : 0];
    assign TX.SOP_POS = out_data[DATA_WIDTH+SOP_POS_WIDTH-1 : DATA_WIDTH];
    assign TX.EOP_POS = out_data[DATA_WIDTH+SOP_POS_WIDTH+EOP_POS_WIDTH-1 : DATA_WIDTH+SOP_POS_WIDTH];
    assign TX.SOP = out_data[DATA_WIDTH+SOP_POS_WIDTH+EOP_POS_WIDTH];
    assign TX.EOP = out_data[DATA_WIDTH+SOP_POS_WIDTH+EOP_POS_WIDTH+1];
    assign TX.SRC_RDY = out_data[DATA_WIDTH+SOP_POS_WIDTH+EOP_POS_WIDTH+2] & out_vld;


    BUSDUMP #(
        .DATA_WIDTH    (TOTAL_WIDTH),
        .STORAGE_ITEMS (ITEMS)
    ) DUMP_U (
        .CLK         (CLK),
        .RESET       (RESET),
        .IN_DATA     (in_data),
        .MI_DWR      (MI_DUMP.DWR ),
        .MI_ADDR     (MI_DUMP.ADDR),
        .MI_RD       (MI_DUMP.RD  ),
        .MI_WR       (MI_DUMP.WR  ),
        .MI_BE       (MI_DUMP.BE  ),
        .MI_DRD      (MI_DUMP.DRD ),
        .MI_ARDY     (MI_DUMP.ARDY),
        .MI_DRDY     (MI_DUMP.DRDY)
    );


    BUSREPLAY #(
        .DATA_WIDTH    (TOTAL_WIDTH),
        .STORAGE_ITEMS (ITEMS)
    ) REPLAY_U (
        .CLK         (CLK),
        .RESET       (RESET),
        .OUT_DATA    (out_data),
        .OUT_VLD     (out_vld),
        .MI_DWR      (MI_REPLAY.DWR ),
        .MI_ADDR     (MI_REPLAY.ADDR),
        .MI_RD       (MI_REPLAY.RD  ),
        .MI_WR       (MI_REPLAY.WR  ),
        .MI_BE       (MI_REPLAY.BE  ),
        .MI_DRD      (MI_REPLAY.DRD ),
        .MI_ARDY     (MI_REPLAY.ARDY),
        .MI_DRDY     (MI_REPLAY.DRDY)
    );


endmodule : DUT
