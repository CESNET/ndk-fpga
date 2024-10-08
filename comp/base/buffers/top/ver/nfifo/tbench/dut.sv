/*
 * DUT.sv: Design under test
 * Copyright (C) 2008 CESNET
 * Author(s): Marcela Simkova <xsimko03@stud.fit.vutbr.cz>
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
   iNFifoRx.fifo_read  FR
);


// -------------------- Module body -------------------------------------------
NFIFO #(
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
    .DATA_OUT           (FR.DATA_OUT),
    .DATA_VLD           (FR.DATA_VLD),
    .RD_BLK_ADDR        (FR.BLOCK_ADDR),
    .READ               (FR.READ),
    .PIPE_EN            (FR.PIPE_EN),
    .EMPTY              (FR.EMPTY),

    .STATUS             (FR.STATUS)
    );

endmodule : DUT
