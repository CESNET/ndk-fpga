// dut.sv: Design under test
// Copyright (C) 2023 CESNET z. s. p. o.
// Author: Tomas Fukac <fukac@cesnet.cz>
//
// SPDX-License-Identifier: BSD-3-Clause

import test_pkg::*;

module DUT (
    input logic CLK,
    input logic RESET,

    iWbRx.dut  WRITE,
    iMvbRx.dut READ,
    iMvbTx.dut READ_OUT,
    iMvbRx.dut MATCH,
    iMvbTx.dut MATCH_OUT
);

    logic [MVB_ITEMS-1 : 0] hit;
    logic [MVB_ITEMS*ITEMS-1 : 0] hit_addr;
    genvar i;

    generate for (i=0; i < MVB_ITEMS; i++) begin
        assign MATCH_OUT.DATA[i*(ITEMS+1)+ITEMS-1 : i*(ITEMS+1)] = hit_addr[(i+1)*ITEMS-1 : i*ITEMS];
        assign MATCH_OUT.DATA[i*(ITEMS+1)+ITEMS] = hit[i];
    end endgenerate

    MVB_TCAM #(
        .MVB_ITEMS          (MVB_ITEMS),
        .DATA_WIDTH         (DATA_WIDTH),
        .ITEMS              (ITEMS),
        .RESOURCES_SAVING   (RESOURCES_SAVING),
        .WRITE_BEFORE_MATCH (WRITE_BEFORE_MATCH),
        .READ_FROM_TCAM     (READ_FROM_TCAM),
        .OUTPUT_READ_REGS   (OUTPUT_READ_REGS),
        .USE_FRAGMENTED_MEM (USE_FRAGMENTED_MEM),
        .DEVICE             (DEVICE)

    ) VHDL_DUT_U (

        // clock and reset
        .CLK                (CLK),
        .RESET              (RESET),

        // read interface
        .READ_ADDR          (READ.DATA),
        .READ_EN            (READ.SRC_RDY),
        .READ_RDY           (READ.DST_RDY),
        // read out
        .READ_DATA          (READ_OUT.DATA[2*DATA_WIDTH-1 : DATA_WIDTH]),
        .READ_MASK          (READ_OUT.DATA[  DATA_WIDTH-1 : 0]),
        .READ_DATA_VLD      (READ_OUT.SRC_RDY),

        // write interface
        .WRITE_DATA         (WRITE.DATA),
        .WRITE_MASK         (WRITE.MASK),
        .WRITE_ADDR         (WRITE.ADDR),
        .WRITE_EN           (WRITE.SRC_RDY),
        .WRITE_RDY          (WRITE.DST_RDY),

        // match interface
        .MATCH_DATA         (MATCH.DATA),
        .MATCH_VLD          (MATCH.VLD),
        .MATCH_SRC_RDY      (MATCH.SRC_RDY),
        .MATCH_DST_RDY      (MATCH.DST_RDY),

        // match out
        //.MATCH_OUT_HIT      (MATCH_OUT.DATA[MVB_ITEMS*ITEMS+MVB_ITEMS-1 : MVB_ITEMS*ITEMS]),
        //.MATCH_OUT_ADDR     (MATCH_OUT.DATA[MVB_ITEMS*ITEMS-1 : 0]),
        .MATCH_OUT_HIT      (hit),
        .MATCH_OUT_ADDR     (hit_addr),
        .MATCH_OUT_VLD      (MATCH_OUT.VLD),
        .MATCH_OUT_SRC_RDY  (MATCH_OUT.SRC_RDY)
    );

    assign READ_OUT.VLD   = 1'b1;

endmodule
