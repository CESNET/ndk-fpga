/*
 * DUT.sv: Design under test
 * Copyright (C) 2007 CESNET
 * Author(s): Petr Kobiersky <kobiersky@liberouter.org>
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
   iFrameLinkRx.dut RX,
   iFrameLinkTx.dut TX,
   iMi32.dut        MI,
   iDiscardStat.dut DS
);

// -------------------- Module body -------------------------------------------
FL_DISCARD_STAT#(
     .DATA_WIDTH      (DATA_WIDTH),
     .CHANNELS        (CHANNELS),
     .STATUS_WIDTH    (STATUS_WIDTH),
     .CNT_WIDTH       (CNT_WIDTH),
     .COUNT_DROP      (COUNT_DROP),
     .COUNT_PASS      (COUNT_PASS),
     .COUNT_DROP_LEN  (COUNT_DROP_LEN),
     .COUNT_PASS_LEN  (COUNT_PASS_LEN),
     .OUTPUT_REG      (OUTPUT_REG)
   )

   VHDL_DUT_U  (
    // Common Interface
     .CLK               (CLK),
     .RESET             (RESET),

    // Write Interface
     .RX_DATA       (RX.DATA),
     .RX_DREM       (RX.DREM),
     .RX_SOF_N      (RX.SOF_N),
     .RX_EOF_N      (RX.EOF_N),
     .RX_SOP_N      (RX.SOP_N),
     .RX_EOP_N      (RX.EOP_N),
     .RX_SRC_RDY_N  (RX.SRC_RDY_N),
     .RX_DST_RDY_N  (DS.DST_RDY_N),

     .RX_CHAN       (DS.RX_CHAN),

    // Read Interface
     .TX_DATA       (TX.DATA),
     .TX_DREM       (TX.DREM),
     .TX_SOF_N      (TX.SOF_N),
     .TX_EOF_N      (TX.EOF_N),
     .TX_SOP_N      (TX.SOP_N),
     .TX_EOP_N      (TX.EOP_N),
     .TX_SRC_RDY_N  (TX.SRC_RDY_N),
//     .TX_DST_RDY_N  (TX.DST_RDY_N),

     .TX_CHAN       (DS.TX_CHAN),

    // Status Interface
     .STATUS        (DS.STATUS),

    // MI32 Interface
     .MI_DWR        (MI.DWR),
     .MI_ADDR       (MI.ADDR),
     .MI_BE         (MI.BE),
     .MI_RD         (MI.RD),
     .MI_WR         (MI.WR),
     .MI_DRDY       (MI.DRDY),
     .MI_ARDY       (MI.ARDY),
     .MI_DRD        (MI.DRD)
);


endmodule : DUT
