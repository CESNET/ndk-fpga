/*
 * DUT.sv: Design under test
 * Copyright (C) 2012 CESNET
 * Author(s): Lukas Kekely <kekely@cesnet.cz>
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
   input logic CLK,
   input logic RESET,
   lengthInterface.dut LENGTH,
   iFrameLinkURx.dut RX,
   iFrameLinkUTx.dut TX
);

// -------------------- Module body -------------------------------------------
trimming_unit_flu #(
     .DATA_WIDTH(DATA_WIDTH),
     .SOP_POS_WIDTH(SOP_POS_WIDTH),
     .LENGTH_WIDTH(LENGTH_WIDTH)
   )

   VHDL_DUT_U  (
    // Common Interface
     .CLK               (CLK),
     .RESET             (RESET),

    // Port 0
     .RX_DATA      (RX.DATA),
     .RX_SOP_POS   (RX.SOP_POS),
     .RX_EOP_POS   (RX.EOP_POS),
     .RX_SOP       (RX.SOP),
     .RX_EOP       (RX.EOP),
     .RX_SRC_RDY   (RX.SRC_RDY),
     .RX_DST_RDY   (RX.DST_RDY),

    // Port 0
     .TX_DATA      (TX.DATA),
     .TX_SOP_POS   (TX.SOP_POS),
     .TX_EOP_POS   (TX.EOP_POS),
     .TX_SOP       (TX.SOP),
     .TX_EOP       (TX.EOP),
     .TX_SRC_RDY   (TX.SRC_RDY),
     .TX_DST_RDY   (TX.DST_RDY),

     .LENGTH       (LENGTH.LENGTH),
     .LENGTH_READY (LENGTH.LENGTH_READY),
     .LENGTH_NEXT  (LENGTH.LENGTH_NEXT)
);


endmodule : DUT
