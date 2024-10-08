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
   input logic[MAX_RATE_L-1:0] RATE,
   output logic PCKT_DISCARD,
   iFrameLinkURx.dut RX,
   iFrameLinkUTx.dut TX,
   iFrameLinkUTx.dut MONITOR
);

// -------------------- Module body -------------------------------------------
flu_sampler #(
     .DATA_WIDTH(RX_DWIDTH),
     .SOP_POS_WIDTH(RX_SOPWIDTH),
     .MAX_RATE(MAX_RATE)
   )

   VHDL_DUT_U  (
    // Common Interface
     .CLK               (CLK),
     .RESET             (RESET),

     .RATE              (RATE),
     .PCKT_DISCARD      (PCKT_DISCARD),

    // Port 0
     .RX_DATA     (RX.DATA),
     .RX_SOP_POS  (RX.SOP_POS),
     .RX_EOP_POS  (RX.EOP_POS),
     .RX_SOP      (RX.SOP),
     .RX_EOP      (RX.EOP),
     .RX_SRC_RDY  (RX.SRC_RDY),
     .RX_DST_RDY  (RX.DST_RDY),

    // Port 0
     .TX_DATA     (TX.DATA),
     .TX_SOP_POS  (TX.SOP_POS),
     .TX_EOP_POS  (TX.EOP_POS),
     .TX_SOP      (TX.SOP),
     .TX_EOP      (TX.EOP),
     .TX_SRC_RDY  (TX.SRC_RDY),
     .TX_DST_RDY  (TX.DST_RDY)
);


endmodule : DUT
