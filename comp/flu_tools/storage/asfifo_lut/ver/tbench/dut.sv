/*
 * DUT.sv: Design under test
 * Copyright (C) 2012 CESNET
 * Author(s): Pavel Benacek <benacek@cesnet.cz>
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
   input logic RX_CLK,
   input logic RX_RESET,
   input logic TX_CLK,
   input logic TX_RESET,
   iFrameLinkURx.dut RX,
   iFrameLinkUTx.dut TX
);

// -------------------- Module body -------------------------------------------
flu_asfifo_lut #(
     .DATA_WIDTH(DATA_WIDTH),
     .SOP_POS_WIDTH(SOP_POS_WIDTH),
     .ITEMS(ITEMS),
     .BLOCK_SIZE(BLOCK_SIZE),
     .STATUS_WIDTH(STATUS_WIDTH)
   )

   VHDL_DUT_U  (
    // Common Interface
     .RX_CLK               (RX_CLK),
     .RX_RESET             (RX_RESET),
     .TX_CLK               (TX_CLK),
     .TX_RESET             (TX_RESET),

    // Port 0
     .RX_DATA     (RX.DATA),
     .RX_SOP_POS  (RX.SOP_POS),
     .RX_EOP_POS  (RX.EOP_POS),
     .RX_SOP      (RX.SOP),
     .RX_EOP      (RX.EOP),
     .RX_SRC_RDY  (RX.SRC_RDY),
     .RX_DST_RDY  (RX.DST_RDY),

    // Port 1
     .TX_DATA     (TX.DATA),
     .TX_SOP_POS  (TX.SOP_POS),
     .TX_EOP_POS  (TX.EOP_POS),
     .TX_SOP      (TX.SOP),
     .TX_EOP      (TX.EOP),
     .TX_SRC_RDY  (TX.SRC_RDY),
     .TX_DST_RDY  (TX.DST_RDY)
);

endmodule : DUT
