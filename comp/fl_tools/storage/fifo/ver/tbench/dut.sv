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
   iFrameLinkFifo.ctrl CTRL
);

// -------------------- Module body -------------------------------------------
FL_FIFO #(
     .DATA_WIDTH    (DATA_WIDTH),
     .USE_BRAMS     (USE_BRAMS),
     .ITEMS         (ITEMS),
     .BLOCK_SIZE    (BLOCK_SIZE),
     .STATUS_WIDTH  (STATUS_WIDTH),
     .PARTS         (PARTS)
   )

   VHDL_DUT_U  (
    // Common Interface
     .CLK               (CLK),
     .RESET             (RESET),

    // Write interface
     .RX_DATA       (RX.DATA),
     .RX_REM        (RX.DREM),
     .RX_SOF_N      (RX.SOF_N),
     .RX_EOF_N      (RX.EOF_N),
     .RX_SOP_N      (RX.SOP_N),
     .RX_EOP_N      (RX.EOP_N),
     .RX_SRC_RDY_N  (RX.SRC_RDY_N),
     .RX_DST_RDY_N  (RX.DST_RDY_N),

    // Read interface
     .TX_DATA       (TX.DATA),
     .TX_REM        (TX.DREM),
     .TX_SOF_N      (TX.SOF_N),
     .TX_EOF_N      (TX.EOF_N),
     .TX_SOP_N      (TX.SOP_N),
     .TX_EOP_N      (TX.EOP_N),
     .TX_SRC_RDY_N  (TX.SRC_RDY_N),
     .TX_DST_RDY_N  (TX.DST_RDY_N),

    // Control interface
     .LSTBLK        (CTRL.LSTBLK),
     .FULL          (CTRL.FULL),
     .EMPTY         (CTRL.EMPTY),
     .STATUS        (CTRL.STATUS),
     .FRAME_RDY     (CTRL.FRAME_RDY)
);


endmodule : DUT
