/*
 * DUT.sv: Design under test
 * Copyright (C) 2015 CESNET
 * Author: Pavel Benacek <benacek@cesnet.cz>
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
   iFrameLinkUEditRx.dut RX,
   iFrameLinkUTx.dut TX
);

// -------------------- Module body -------------------------------------------
MAC_EDITOR #(
     .DATA_WIDTH    (DATA_WIDTH),
     .SOP_POS_WIDTH (SOP_POS_WIDTH)
   )

   VHDL_DUT_U  (
      // Common Interface
     .CLK         (CLK),
     .RESET       (RESET),

      // Write Port
     .RX_DATA     (RX.DATA),
     .RX_SOP_POS  (RX.SOP_POS),
     .RX_EOP_POS  (RX.EOP_POS),
     .RX_SOP      (RX.SOP),
     .RX_EOP      (RX.EOP),
     .RX_SRC_RDY  (RX.SRC_RDY),
     .RX_DST_RDY  (RX.DST_RDY),

     .DST_DATA    (RX.DST_DATA),
     .DST_MASK    (RX.DST_MASK),
     .DST_W       (RX.DST_W),

     .SRC_DATA    (RX.SRC_DATA),
     .SRC_MASK    (RX.SRC_MASK),
     .SRC_W       (RX.SRC_W),

     // Read Port
     .TX_DATA     (TX.DATA),
     .TX_SOP_POS  (TX.SOP_POS),
     .TX_EOP_POS  (TX.EOP_POS),
     .TX_SOP      (TX.SOP),
     .TX_EOP      (TX.EOP),
     .TX_SRC_RDY  (TX.SRC_RDY),
     .TX_DST_RDY  (TX.DST_RDY)
   );

endmodule : DUT
