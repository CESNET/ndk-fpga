/*
 * file       : dut.sv
 * Copyright (C) 2022 CESNET z. s. p. o.
 * description: DUT - Block Lock
 * date       : 2022
 * author     : Oliver Gurka <xgurka00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import test::*;

module DUT
    (
        input logic CLK,
        reset_if.dut rst_if,
        mvb_if.dut_rx mvb_wr,
        mvb_if.dut_tx mvb_rd
    );

    logic RX_HEADER_VALID;

    logic RX_LOCK_AQUIRED;
    logic SLIP_CMD;

    assign RX_HEADER_VALID = mvb_wr.SRC_RDY;

    assign mvb_rd.SRC_RDY = 2'b1;
    assign mvb_rd.DST_RDY = 2'b1;
    assign mvb_rd.VLD[0] = 2'b1;

    assign mvb_rd.DATA[0] = RX_LOCK_AQUIRED;
    assign mvb_rd.DATA[1] = SLIP_CMD;

    BLOCK_LOCK #(
        .SH_CNT_MAX         (SH_CNT_MAX),
        .SH_INVALID_CNT_MAX (SH_INVALID_CNT_MAX),
        .SLIP_WAIT_TIME     (SLIP_WAIT_TIME),
        .SLIP_PULSE         (SLIP_PULSE)
    ) VHDL_DUT_U (
        .CLK                (CLK),
        .RST                (rst_if.RESET),
        .RX_HEADER_IN       (mvb_wr.DATA),
        .RX_HEADER_VALID    (RX_HEADER_VALID),
        .RX_LOCK_AQUIRED    (RX_LOCK_AQUIRED),
        .SLIP_CMD           (SLIP_CMD)
    );

endmodule
