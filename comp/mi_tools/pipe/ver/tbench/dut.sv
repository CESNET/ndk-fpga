//-- dut.sv: Design Under Test
//-- Copyright (C) 2021 CESNET z. s. p. o.
//-- Author(s): Tomáš Beneš <xbenes55@stud.fit.vutbr.cz>

//-- SPDX-License-Identifier: BSD-3-Clause


import test_pkg::*;

module DUT (
    input logic CLK,
    input logic RESET,
    iMi.master  MI_MASTER,
    iMi.slave   MI_SLAVE

);

    MI_PIPE #(

    ) VHDL_DUT_U (
        .CLK         (CLK),
        .RESET       (RESET),

        // Input MI interface
        .IN_DWR         (MI_MASTER.DWR ),
        .IN_MWR         (MI_MASTER.MWR ),
        .IN_ADDR        (MI_MASTER.ADDR),
        .IN_RD          (MI_MASTER.RD  ),
        .IN_WR          (MI_MASTER.WR  ),
        .IN_BE          (MI_MASTER.BE  ),
        .IN_DRD         (MI_MASTER.DRD ),
        .IN_ARDY        (MI_MASTER.ARDY),
        .IN_DRDY        (MI_MASTER.DRDY),

        // Output MI interface
        .OUT_DWR        (MI_SLAVE.DWR ),
        .OUT_MWR        (MI_SLAVE.MWR ),
        .OUT_ADDR       (MI_SLAVE.ADDR),
        .OUT_RD         (MI_SLAVE.RD  ),
        .OUT_WR         (MI_SLAVE.WR  ),
        .OUT_BE         (MI_SLAVE.BE  ),
        .OUT_DRD        (MI_SLAVE.DRD ),
        .OUT_ARDY       (MI_SLAVE.ARDY),
        .OUT_DRDY       (MI_SLAVE.DRDY)
    );

endmodule
