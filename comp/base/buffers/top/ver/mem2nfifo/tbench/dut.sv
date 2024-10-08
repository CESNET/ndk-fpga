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
   iNFifoTx.mem_write  MW,
   iNFifoTx.nfifo_read  FR[FLOWS],
   iNFifoTx.nfifo_read  MONITOR[FLOWS]
);


// Signals for DUT conection
wire [DATA_WIDTH-1:0] fr_data_out;
wire [FLOWS-1:0] fr_data_vld;
wire [FLOWS-1:0] fr_read;
wire [FLOWS-1:0] fr_empty;
wire [$clog2(BLOCK_SIZE+1)*FLOWS-1:0] mv_status;
genvar i;

// Connecting FR to interfaces
generate
for (i=0; i<FLOWS; i++) begin
  assign FR[i].DATA_OUT  = fr_data_out[(i+1)*(DATA_WIDTH/FLOWS)-1:(DATA_WIDTH/FLOWS)*i];
  assign FR[i].DATA_VLD  = fr_data_vld[i];
  assign fr_read[i]      = FR[i].READ;
  assign FR[i].EMPTY     = fr_empty[i];
//  assign MW[i].STATUS    = mv_status[(i+1)*$clog2(BLOCK_SIZE+1)-1:$clog2(BLOCK_SIZE+1)*i];
  end
endgenerate

// -------------------- Module body -------------------------------------------
MEM2NFIFO #(
        .DATA_WIDTH     (DATA_WIDTH),
        .FLOWS          (FLOWS),
        .BLOCK_SIZE     (BLOCK_SIZE),
        .LUT_MEMORY     (LUT_MEMORY),
        .GLOB_STATE     (GLOB_STATE)
   )

   VHDL_DUT_U (
    // Common Interface

    //vyber signalov
    .CLK               (CLK),
    .RESET             (RESET),

    // Write interface
    .DATA_IN            (MW.DATA_IN),
    .BLOCK_ADDR         (MW.BLOCK_ADDR),
    .WR_ADDR            (MW.WR_ADDR),
    .NEW_LEN            (MW.NEW_LEN),
    .NEW_LEN_DV         (MW.NEW_LEN_DV),
    .WRITE              (MW.WRITE),
    .FULL               (MW.FULL),
    .STATUS             (MW.STATUS_F),

    // Read interface
    .DATA_OUT           (fr_data_out),
    .DATA_VLD           (fr_data_vld),
    .READ               (fr_read),
    .EMPTY              (fr_empty)

   // .STATUS             (fr_status)
    );

endmodule : DUT
