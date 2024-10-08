/*
 * DUT.sv: Design under test
 * Copyright (C) 2010 CESNET
 * Author(s): Marek Santa <santa@liberouter.org>
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
// obsahuje pouzite parametre
import test_pkg::*; // Test constants

module DUT (
   input logic CLK,
   input logic RESET,
   iNFifoTx.fifo_write FW,
   iMemRead.dut        MR
);


// -------------------- Module body -------------------------------------------
MFIFO2MEM #(
        .DATA_WIDTH     (DATA_WIDTH),
        .FLOWS          (FLOWS),
        .BLOCK_SIZE     (BLOCK_SIZE),
        .LUT_MEMORY     (LUT_MEMORY),
        .OUTPUT_REG     (OUTPUT_REG)
   )

   VHDL_DUT_U (
    // Common Interface

    //vyber signalov
    .CLK               (CLK),
    .RESET             (RESET),

    // Write interface
    .DATA_IN            (FW.DATA_IN),
    .WR_BLK_ADDR        (FW.BLOCK_ADDR),
    .WRITE              (FW.WRITE),
    .FULL               (FW.FULL),

    // Read interface
    .DATA_OUT           (MR.DATA_OUT),
    .DATA_VLD           (MR.DATA_VLD),
    .RD_BLK_ADDR        (MR.BLOCK_ADDR),
    .RD_ADDR            (MR.RD_ADDR),
    .READ               (MR.READ),
    .REL_LEN            (MR.REL_LEN),
    .REL_LEN_DV         (MR.REL_LEN_DV),
    .PIPE_EN            (MR.PIPE_EN),
    .EMPTY              (MR.EMPTY),

    .STATUS             (MR.STATUS)
    );

endmodule : DUT
