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
    iMi32.dut MI,
    iMvbRx.dut RX,
    iMvbTx.dut TX
);

    DUT_WRAPPER #(
        .ITEMS         (ITEMS),
        .ITEM_WIDTH    (ITEM_WIDTH),
        .SRC_CHANNELS  (SRC_CHANNELS),
        .DST_CHANNELS  (DST_CHANNELS),
        .MI_DATA_WIDTH (MI_DATA_WIDTH),
        .MI_ADDR_WIDTH (MI_ADDR_WIDTH),
        .DEVICE        (DEVICE)
    ) VHDL_DUT_U (
        .CLK           (CLK),
        .RESET         (RESET),

        .MI_DWR        (MI.DWR),
        .MI_ADDR       (MI.ADDR),
        .MI_RD         (MI.RD),
        .MI_WR         (MI.WR),
        .MI_BE         (MI.BE),
        .MI_DRD        (MI.DRD),
        .MI_ARDY       (MI.ARDY),
        .MI_DRDY       (MI.DRDY),

        .RX_DATA       (RX.DATA),
        .RX_VLD        (RX.VLD),
        .RX_SRC_RDY    (RX.SRC_RDY),
        .RX_DST_RDY    (RX.DST_RDY),

        .TX_DATA       (TX.DATA),
        .TX_VLD        (TX.VLD),
        .TX_SRC_RDY    (TX.SRC_RDY),
        .TX_DST_RDY    (TX.DST_RDY)
    );

endmodule
