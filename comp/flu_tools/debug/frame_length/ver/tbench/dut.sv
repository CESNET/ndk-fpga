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

import test_pkg::*; // Test constants

module DUT (
  input logic CLK,
  input logic RESET,
  iFrameLinkURx.dut RX,
  iWordLinkTx.dut TX
);

  FLU_FRAME_LENGTH #(
    .USE_INREG     (0),
    .USE_OUTREG    (0),
    .DATA_WIDTH    (DATA_WIDTH),
    .SOP_POS_WIDTH (SOP_POS_WIDTH)
  ) VHDL_DUT_U (
    .CLK         (CLK),
    .RESET       (RESET),
    .RX_SOP_POS  (RX.SOP_POS),
    .RX_EOP_POS  (RX.EOP_POS),
    .RX_SOP      (RX.SOP),
    .RX_EOP      (RX.EOP),
    .RX_SRC_RDY  (RX.SRC_RDY),
    .RX_DST_RDY  (TX.DST_RDY),
    .LENGTH      (TX.DATA),
    .LENGTH_VLD  (TX.SRC_RDY)
  );
  assign RX.DST_RDY = TX.DST_RDY;

endmodule : DUT
