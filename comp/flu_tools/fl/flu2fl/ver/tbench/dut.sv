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

//V PRIPADE POTREBY SA MOZE DOPLNIT VIAC FRAMELINKOVYCH ROZHRANI DANEHO TYPU
module DUT (
   input logic CLK,
   input logic RESET,
   iFrameLinkURx.dut RX,
   iFrameLinkTx.dut TX,
   iFrameLinkTx.dut MONITOR
);

// -------------------- Module body -------------------------------------------
//TODO: ZMENA NAZVU TESTOVANEJ KOMPONENTY, V PRIPADE PRIDANIA ROZHRANI TREBA PRIDAT AJ PORTY
flu2fl #(
     .DATA_WIDTH(RX_DWIDTH),
     .SOP_POS_WIDTH(RX_SOPWIDTH),
     .IN_PIPE_EN(RX_FALSE),
     .IN_PIPE_OUTREG(RX_FALSE),
     .OUT_PIPE_EN(RX_FALSE),
     .OUT_PIPE_OUTREG(RX_FALSE)
   )

   VHDL_DUT_U  (
    // Common Interface
     .CLK               (CLK),
     .RESET             (RESET),

    // Port 0
     .RX_DATA     (RX.DATA),
     .RX_SOP_POS  (RX.SOP_POS),
     .RX_EOP_POS  (RX.EOP_POS),
     .RX_SOP      (RX.SOP),
     .RX_EOP      (RX.EOP),
     .RX_SRC_RDY  (RX.SRC_RDY),
     .RX_DST_RDY  (RX.DST_RDY),

    // Port 0
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
