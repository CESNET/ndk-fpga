/*!
 * \file dut.sv
 * \brief Design Under Test
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2018
 */
 /*
 * Copyright (C) 2018 CESNET
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */


module DUT (
    input logic                 CLK,
    input logic                 RESET,
    iMi32.dut                   MI
);

    top_ver VHDL_DUT_U (
        .CLK               (CLK),
        .RESET             (RESET),
        .MI_DWR            (MI.DWR ),
        .MI_ADDR           (MI.ADDR),
        .MI_RD             (MI.RD  ),
        .MI_WR             (MI.WR  ),
        .MI_BE             (MI.BE  ),
        .MI_DRD            (MI.DRD ),
        .MI_ARDY           (MI.ARDY),
        .MI_DRDY           (MI.DRDY)
    );

endmodule
