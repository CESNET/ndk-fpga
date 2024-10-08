/*!
 * \file dut.sv
 * \brief Design Under Test
 * \author Jakub Cabal <cabal@cesnet.cz>
 * \date 2017
 */
 /*
 * Copyright (C) 2017 CESNET z. s. p. o.
 *
 * LICENSE TERMS
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import test_pkg::*;

module DUT (
   input logic FLU_CLK,
   input logic FLU_RESET,
   input logic CMAC_CLK,
   input logic CMAC_RESET,
   input logic MI_CLK,
   input logic MI_RESET,

   iFrameLinkURx.dut RX,
   iLbusTx.dut       TX,
   iMi32.dut         MI
);

   DUT_WRAPPER #(
   ) VHDL_DUT_U (
      .FLU_CLK     (FLU_CLK),
      .FLU_RESET   (FLU_RESET),
      .RX_DATA     (RX.DATA),
      .RX_SOP_POS  (RX.SOP_POS),
      .RX_EOP_POS  (RX.EOP_POS),
      .RX_SOP      (RX.SOP),
      .RX_EOP      (RX.EOP),
      .RX_SRC_RDY  (RX.SRC_RDY),
      .RX_DST_RDY  (RX.DST_RDY),

      .MI_CLK      (MI_CLK),
      .MI_RESET    (MI_RESET),
      .MI_DWR      (MI.DWR),
      .MI_ADDR     (MI.ADDR),
      .MI_RD       (MI.RD),
      .MI_WR       (MI.WR),
      .MI_BE       (MI.BE),
      .MI_DRD      (MI.DRD),
      .MI_ARDY     (MI.ARDY),
      .MI_DRDY     (MI.DRDY),

      .CMAC_CLK    (CMAC_CLK),
      .CMAC_RESET  (CMAC_RESET),
      .TX_DATA     (TX.DATA),
      .TX_SOP      (TX.SOP),
      .TX_EOP      (TX.EOP),
      .TX_MTY      (TX.MTY),
      .TX_ENA      (TX.ENA),
      .TX_RDY      (TX.RDY)
   );

endmodule
