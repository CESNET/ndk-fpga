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
   input logic RESET,
   input logic RX_CLK,
   iFrameLinkURx.dut RX,
   input logic TX_CLK,
   iFrameLinkUTx.dut TX
);


    FLU_ASFIFO_BRAM_XILINX #(
        .DEVICE        (DEVICE),
        .DATA_WIDTH    (DATA_WIDTH),
        .SOP_POS_WIDTH (SOP_POS_WIDTH),
        .ITEMS         (ITEMS)
    ) VHDL_DUT_U  (
        .RX_CLK      (RX_CLK),
        .RX_RESET    (RESET),
        .RX_DATA     (RX.DATA),
        .RX_SOP_POS  (RX.SOP_POS),
        .RX_EOP_POS  (RX.EOP_POS),
        .RX_SOP      (RX.SOP),
        .RX_EOP      (RX.EOP),
        .RX_SRC_RDY  (RX.SRC_RDY),
        .RX_DST_RDY  (RX.DST_RDY),
        .TX_CLK      (TX_CLK),
        .TX_RESET    (TX_RESET),
        .TX_DATA     (TX.DATA),
        .TX_SOP_POS  (TX.SOP_POS),
        .TX_EOP_POS  (TX.EOP_POS),
        .TX_SOP      (TX.SOP),
        .TX_EOP      (TX.EOP),
        .TX_SRC_RDY  (TX.SRC_RDY),
        .TX_DST_RDY  (TX.DST_RDY)
    );

endmodule
