/*
 * dut.sv: Design under test
 * Copyright (C) 2018 CESNET
 * Author(s): Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 */

import test_pkg::*; // Test constants



module DUT (
    input logic CLK,
    input logic RESET,
    iFrameLinkUTx.dut TX,
    iMi32.dut MI
);

  FLU_GENERATOR #(
    .CHANNELS          (1),
    .FLU_WIDTH         (DATA_WIDTH),
    .SOP_WIDTH         (SOP_POS_WIDTH)
  ) VHDL_DUT_U (
    .RESET             (RESET),
    .CLK               (CLK),
    .FLU_CHANNEL  (),
    .FLU_DATA     (TX.DATA),
    .FLU_SOP_POS  (TX.SOP_POS),
    .FLU_EOP_POS  (TX.EOP_POS),
    .FLU_SOP      (TX.SOP),
    .FLU_EOP      (TX.EOP),
    .FLU_SRC_RDY  (TX.SRC_RDY),
    .FLU_DST_RDY  (TX.DST_RDY),
    .MI_DWR             (MI.DWR),
    .MI_ADDR            (MI.ADDR),
    .MI_BE              (MI.BE),
    .MI_RD              (MI.RD),
    .MI_WR              (MI.WR),
    .MI_DRD             (MI.DRD),
    .MI_ARDY            (MI.ARDY),
    .MI_DRDY            (MI.DRDY)
  );

endmodule
