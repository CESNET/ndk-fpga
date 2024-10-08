/*!
 * \file dut.sv
 * \brief Design Under Test
 * \author Daniel Kříž <xkrizd01@vutbr.cz>
 * \date 2020
 */
 /*
 * Copyright (C) 2020 CESNET z. s. p. o.
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
    iMvbRx.dut RX,
    iMvbTx.dut TX
);

    SHAKEDOWN #(
        .INPUTS       (INPUTS),
        .OUTPUTS      (OUTPUTS),
        .DATA_WIDTH   (DATA_WIDTH),
        .OUTPUT_REG   (OUTPUT_REG)
    ) VHDL_DUT_U (
        .CLK          (CLK),
        .RESET        (RESET),

        .DIN          (RX.DATA),
        .DIN_VLD      (RX.VLD),
        .DIN_SRC_RDY  (RX.SRC_RDY),
        .DIN_DST_RDY  (RX.DST_RDY),

        .DOUT         (TX.DATA),
        .DOUT_VLD     (TX.VLD),
        .DOUT_SRC_RDY (TX.SRC_RDY),
        .DOUT_DST_RDY (TX.DST_RDY)
    );

endmodule
