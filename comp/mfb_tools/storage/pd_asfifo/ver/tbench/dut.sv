/*!
 * \file dut.sv
 * \brief Design Under Test
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2018
 */
 /*
 * Copyright (C) 2018 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

import test_pkg::*;
import math_pkg::*;

module DUT (
   input logic RX_CLK,
   input logic RX_RESET,
   input logic TX_CLK,
   input logic TX_RESET,
   iMfbRx.dut RX,
   iMfbTx.dut TX,
   iMvbRx.dut FD_RX,
   iMvbTx.dut FD_TX
);

logic in_force_discard;
logic out_force_discard;

assign in_force_discard = FD_RX.DATA & FD_RX.SRC_RDY;

FORCE_DISCARD #(
   .REGIONS (REGIONS)
) FORCE_DISCARD_I (
   .CLK                (RX_CLK),
   .RESET              (RX_RESET),
   .IN_SOF             (RX.SOF),
   .IN_EOF             (RX.EOF),
   .IN_SRC_RDY         (RX.SRC_RDY),
   .IN_DST_RDY         (RX.DST_RDY),
   .IN_FORCE_DISCARD   (in_force_discard),
   .OUT_FORCE_DISCARD  (out_force_discard),
   .OUT_PKT_FD         (FD_TX.DATA),
   .OUT_PKT_FD_VLD     (FD_TX.VLD),
   .OUT_PKT_FD_SRC_RDY (FD_TX.SRC_RDY)
);

assign FD_RX.DST_RDY = 1'b1;

MFB_PD_ASFIFO #(
   .ITEMS       (ITEMS),
   .REGIONS     (REGIONS),
   .REGION_SIZE (REGION_SIZE),
   .BLOCK_SIZE  (BLOCK_SIZE),
   .ITEM_WIDTH  (ITEM_WIDTH)
) VHDL_DUT_U (
   // RX MFB INTERFACE
   .RX_CLK           (RX_CLK),
   .RX_RESET         (RX_RESET),
   .RX_DATA          (RX.DATA),
   .RX_SOF_POS       (RX.SOF_POS),
   .RX_EOF_POS       (RX.EOF_POS),
   .RX_SOF           (RX.SOF),
   .RX_EOF           (RX.EOF),
   .RX_SRC_RDY       (RX.SRC_RDY),
   .RX_DST_RDY       (RX.DST_RDY),
   .RX_DISCARD       (RX.META),
   .RX_FORCE_DISCARD (out_force_discard),
   .STATUS           (),
   // TX MFB INTERFACE
   .TX_CLK     (TX_CLK),
   .TX_RESET   (TX_RESET),
   .TX_DATA    (TX.DATA),
   .TX_SOF_POS (TX.SOF_POS),
   .TX_EOF_POS (TX.EOF_POS),
   .TX_SOF     (TX.SOF),
   .TX_EOF     (TX.EOF),
   .TX_SRC_RDY (TX.SRC_RDY),
   .TX_DST_RDY (TX.DST_RDY)
);

endmodule
