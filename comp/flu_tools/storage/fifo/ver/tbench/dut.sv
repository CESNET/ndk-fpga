/*
 * DUT.sv: Design under test
 * Copyright (C) 2012 CESNET
 * Author: Lukas Kekely <kekely@cesnet.cz>
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
   iFrameLinkURx.dut RX,
   iFrameLinkUTx.dut TX,
   iFrameLinkUFifo.ctrl CTRL
);

// -------------------- Module body -------------------------------------------
FLU_FIFO #(
     .DATA_WIDTH    (DATA_WIDTH),
     .SOP_POS_WIDTH (SOP_POS_WIDTH),
     .USE_BRAMS     (USE_BRAMS),
     .ITEMS         (ITEMS),
     .BLOCK_SIZE    (BLOCK_SIZE),
     .STATUS_WIDTH  (STATUS_WIDTH)
   )

   VHDL_DUT_U  (
    // Common Interface
     .CLK               (CLK),
     .RESET             (RESET),

    // Write Port
     .RX_DATA     (RX.DATA),
     .RX_SOP_POS  (RX.SOP_POS),
     .RX_EOP_POS  (RX.EOP_POS),
     .RX_SOP      (RX.SOP),
     .RX_EOP      (RX.EOP),
     .RX_SRC_RDY  (RX.SRC_RDY),
     .RX_DST_RDY  (RX.DST_RDY),

    // Read Port
     .TX_DATA     (TX.DATA),
     .TX_SOP_POS  (TX.SOP_POS),
     .TX_EOP_POS  (TX.EOP_POS),
     .TX_SOP      (TX.SOP),
     .TX_EOP      (TX.EOP),
     .TX_SRC_RDY  (TX.SRC_RDY),
     .TX_DST_RDY  (TX.DST_RDY),

    // Control interface
     .LSTBLK        (CTRL.LSTBLK),
     .FULL          (CTRL.FULL),
     .EMPTY         (CTRL.EMPTY),
     .STATUS        (CTRL.STATUS),
     .FRAME_RDY     (CTRL.FRAME_RDY)
);


endmodule : DUT
