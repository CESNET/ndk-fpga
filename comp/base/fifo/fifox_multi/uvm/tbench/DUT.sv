// dut.sv: Design under test
// Copyright (C) 2023 CESNET z. s. p. o.
// Author(s): Yaroslav Marushchenko <xmarus09@stud.fit.vutbr.cz>

// SPDX-License-Identifier: BSD-3-Clause

import test::*;

module DUT (
    input logic CLK,
    input logic RST,
    mvb_if.dut_rx mvb_rx,
    mvb_if.dut_rx mvb_rd,
    mvb_if.dut_tx mvb_tx,
    mvb_if.dut_tx mvb_status
);

    if (IMPL_SHAKEDOWN == "FULL") begin : gen_probe
        bind FIFOX_MULTI : VHDL_DUT_U probe_inf #(
            1 + $clog2(WRITE_PORTS + 1) + $clog2(READ_PORTS + 1)
        ) probe_status (
            .event_signal ((RESET === 1'b0)),
            .event_data   ({
                fifox_multi_full_g.fifox_multi_full_i.in_reg1_en,
                fifox_multi_full_g.fifox_multi_full_i.wr_num_reg1,
                fifox_multi_full_g.fifox_multi_full_i.rd_num
            }),
            .CLK          (CLK)
        );
    end : gen_probe
    logic [WRITE_PORTS-1 : 0] wr;
    logic full;

    logic [READ_PORTS*DATA_WIDTH-1 : 0] dout;
    logic [READ_PORTS           -1 : 0] rd_continuous;
    logic [READ_PORTS           -1 : 0] empty;

    logic aempty;
    logic afull;

    FIFOX_MULTI #(

        .DATA_WIDTH          (DATA_WIDTH         ),
        .ITEMS               (ITEMS              ),
        .WRITE_PORTS         (WRITE_PORTS        ),
        .READ_PORTS          (READ_PORTS         ),
        .RAM_TYPE            (RAM_TYPE           ),
        .DEVICE              (DEVICE             ),
        .ALMOST_FULL_OFFSET  (ALMOST_FULL_OFFSET ),
        .ALMOST_EMPTY_OFFSET (ALMOST_EMPTY_OFFSET),
        .ALLOW_SINGLE_FIFO   (ALLOW_SINGLE_FIFO  ),
        .SAFE_READ_MODE      (SAFE_READ_MODE     ),
        .FIFOX_MULTI_ARCH    (IMPL_SHAKEDOWN     )

    ) VHDL_DUT_U (

        .CLK   (CLK),
        .RESET (RST),

        .DI    (mvb_rx.DATA),
        .WR    (wr         ),
        .FULL  (full       ),
        .AFULL (afull      ),

        .DO     (mvb_tx.DATA  ),
        .RD     (rd_continuous),
        .EMPTY  (empty        ),
        .AEMPTY (aempty       )

    );

    assign wr = mvb_rx.VLD & { WRITE_PORTS { mvb_rx.SRC_RDY } };
    assign mvb_rx.DST_RDY = ~full;

    assign mvb_tx.VLD = rd_continuous & (~empty);
    assign mvb_tx.SRC_RDY = |(~empty);
    assign mvb_tx.DST_RDY = |rd_continuous;

    assign mvb_status.DATA = { afull, aempty };
    assign mvb_status.VLD = (RST === 1'b0);
    assign mvb_status.SRC_RDY = 1;
    assign mvb_status.DST_RDY = 1;

    always_comb begin
        logic [READ_PORTS-1 : 0] tmp;

        tmp[0] = mvb_rd.VLD[0] === 1'b1;
        for (int unsigned it = 1; it < READ_PORTS; it++) begin
            tmp[it] = tmp[it-1] && mvb_rd.VLD[it] === 1'b1;
        end
        rd_continuous = SAFE_READ_MODE ? tmp : tmp & (~empty);
    end

    assign mvb_rd.DST_RDY = 1;

endmodule
