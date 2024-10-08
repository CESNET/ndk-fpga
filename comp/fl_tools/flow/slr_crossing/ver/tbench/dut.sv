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
  iFrameLinkRx.dut RX,
  iFrameLinkTx.dut TX
);

FL_SLR_CROSSING #(
  .USE_OUTREG(USE_OUTREG),
  .DATA_WIDTH(DATA_WIDTH)
) VHDL_DUT_U (
  .CLK               (CLK),
  .RX_RESET          (RESET),

  .RX_DATA       (RX.DATA),
  .RX_DREM       (RX.DREM),
  .RX_SOF_N      (RX.SOF_N),
  .RX_EOF_N      (RX.EOF_N),
  .RX_SOP_N      (RX.SOP_N),
  .RX_EOP_N      (RX.EOP_N),
  .RX_SRC_RDY_N  (RX.SRC_RDY_N),
  .RX_DST_RDY_N  (RX.DST_RDY_N),

  .TX_RESET      (RESET),

  .TX_DATA       (TX.DATA),
  .TX_DREM       (TX.DREM),
  .TX_SOF_N      (TX.SOF_N),
  .TX_EOF_N      (TX.EOF_N),
  .TX_SOP_N      (TX.SOP_N),
  .TX_EOP_N      (TX.EOP_N),
  .TX_SRC_RDY_N  (TX.SRC_RDY_N),
  .TX_DST_RDY_N  (TX.DST_RDY_N)
);

endmodule : DUT
