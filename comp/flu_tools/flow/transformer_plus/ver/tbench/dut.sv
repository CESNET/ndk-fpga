/*
 * DUT.sv: Design under test
 * Copyright (C) 2013 CESNET
 * Author: Lukas Kekely <kekely@cesnet.cz>
 *
 * SPDX-License-Identifier: BSD-3-Clause
 *
 */

// ----------------------------------------------------------------------------
//                        Module declaration
// ----------------------------------------------------------------------------
import test_pkg::*; // Test constants

module DUT (
   input logic CLK,
   input logic RESET,
   iFrameLinkUPRx.dut RX,
   iFrameLinkUPTx.dut TX
);


// -------------------- Module body -------------------------------------------
FLU_TRANSFORMER_PLUS #(
     .HEADER_WIDTH     (HEADER_WIDTH),
     .CHANNEL_WIDTH    (CHANNEL_WIDTH),
     .RX_DATA_WIDTH    (RX_DATA_WIDTH),
     .RX_SOP_POS_WIDTH (RX_SOP_POS_WIDTH),
     .TX_DATA_WIDTH    (TX_DATA_WIDTH),
     .TX_SOP_POS_WIDTH (TX_SOP_POS_WIDTH)
   )

   VHDL_DUT_U  (
    // Common Interface
     .CLK               (CLK),
     .RESET             (RESET),

    // Write Port
     .RX_HEADER   (RX.HEADER),
     .RX_CHANNEL  (RX.CHANNEL),
     .RX_DATA     (RX.DATA),
     .RX_SOP_POS  (RX.SOP_POS),
     .RX_EOP_POS  (RX.EOP_POS),
     .RX_SOP      (RX.SOP),
     .RX_EOP      (RX.EOP),
     .RX_SRC_RDY  (RX.SRC_RDY),
     .RX_DST_RDY  (RX.DST_RDY),

    // Read Port
     .TX_HEADER   (TX.HEADER),
     .TX_DATA     (TX.DATA),
     .TX_SOP_POS  (TX.SOP_POS),
     .TX_EOP_POS  (TX.EOP_POS),
     .TX_SOP      (TX.SOP),
     .TX_EOP      (TX.EOP),
     .TX_SRC_RDY  (TX.SRC_RDY),
     .TX_DST_RDY  (TX.DST_RDY)
);


endmodule : DUT
