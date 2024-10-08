// dut.sv
// Copyright (C) 2019 CESNET z. s. p. o.
// Author(s): Lukas Hejcman <xhejcm01@stud.fit.vutbr.cz>
//
// SPDX-License-Identifier: BSD-3-Clause


import test_pkg::*;

module DUT (
    input logic CLK,
    input logic RESET,
    iMi32.dut   MI
);

SENSOR_INTERFACE #(
    .VERI       (1)
)

VHDL_DUT_U (
    .CLK        (CLK),
    .RESET      (RESET),
    .DWR        (MI.DWR ),
    .ADDR       (MI.ADDR),
    .RD         (MI.RD  ),
    .WR         (MI.WR  ),
    .BE         (MI.BE  ),
    .DRD        (MI.DRD ),
    .ARDY       (MI.ARDY),
    .DRDY       (MI.DRDY)
);

endmodule
