/*
 * DUT.sv: Design under test
 * Copyright (C) 2014 CESNET
 * Author: Vaclav Hummel <xhumme00@stud.fit.vutbr.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 * $Id$
 *
 * TODO:
 *
 */

// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

module DUT (
   input logic APP_CLK,
   input logic APP_RST,
   input logic QDR_CLK,
   input logic QDR_RST,
   iFrameLinkURx.dut RX,
   iFrameLinkUTx.dut TX
);

// -------------------- Module body -------------------------------------------
   FLU_QDR #()
   VHDL_DUT_U  (
    // Common Interface
     .APP_CLK               (APP_CLK),
     .APP_RST             (APP_RST),

     .QDR_CLK               (QDR_CLK),
     .QDR_RST             (QDR_RST),

    // Write Port
     .FLU_RX_DATA     (RX.DATA),
     .FLU_RX_SOP_POS  (RX.SOP_POS),
     .FLU_RX_EOP_POS  (RX.EOP_POS),
     .FLU_RX_SOP      (RX.SOP),
     .FLU_RX_EOP      (RX.EOP),
     .FLU_RX_SRC_RDY  (RX.SRC_RDY),
     .FLU_RX_DST_RDY  (RX.DST_RDY),

    // Read Port
     .FLU_TX_DATA     (TX.DATA),
     .FLU_TX_SOP_POS  (TX.SOP_POS),
     .FLU_TX_EOP_POS  (TX.EOP_POS),
     .FLU_TX_SOP      (TX.SOP),
     .FLU_TX_EOP      (TX.EOP),
     .FLU_TX_SRC_RDY  (TX.SRC_RDY),
     .FLU_TX_DST_RDY  (TX.DST_RDY)
);


endmodule : DUT
