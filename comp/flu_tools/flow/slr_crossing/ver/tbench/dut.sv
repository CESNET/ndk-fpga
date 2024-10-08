/*!
 * \file dut.sv
 * \brief Design Under Test
 * \author Lukas Kekely <kekely@cesnet.cz>
 * \date 2014
 */
/*
 * Copyright (C) 2014 CESNET
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
  iFrameLinkUTx.dut TX
);

FLU_SLR_CROSSING #(
  .USE_OUTREG    (USE_OUTREG),
  .DATA_WIDTH    (DATA_WIDTH),
  .SOP_POS_WIDTH (SOP_POS_WIDTH)
) VHDL_DUT_U (
  .CLK               (CLK),

  .RX_RESET    (RESET),
  .RX_DATA     (RX.DATA),
  .RX_SOP_POS  (RX.SOP_POS),
  .RX_EOP_POS  (RX.EOP_POS),
  .RX_SOP      (RX.SOP),
  .RX_EOP      (RX.EOP),
  .RX_SRC_RDY  (RX.SRC_RDY),
  .RX_DST_RDY  (RX.DST_RDY),

  .TX_RESET    (RESET),
  .TX_DATA     (TX.DATA),
  .TX_SOP_POS  (TX.SOP_POS),
  .TX_EOP_POS  (TX.EOP_POS),
  .TX_SOP      (TX.SOP),
  .TX_EOP      (TX.EOP),
  .TX_SRC_RDY  (TX.SRC_RDY),
  .TX_DST_RDY  (TX.DST_RDY)
);

endmodule : DUT
